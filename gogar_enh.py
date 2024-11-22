#!/usr/bin/env python3
# gogar.py - GOGAR in Python with enhancements
#
#   GOGAR - the game of giving and asking for reasons.
#   A partial simulation of the scorekeeping dynamics from Chapter 3
#   of Robert Brandom's book Making It Explicit (Harvard, 1994).
#   Adapted from Gogar.rb - gogar in ruby (c) 2006 John MacFarlane. 
#   This software carries no warranties of any kind.

import re
import sys
import argparse
from collections import deque
import threading
import difflib
import readline  # For editable input and history
import os

# Check if the platform supports ANSI escape codes
if os.name == 'nt':
    import ctypes
    kernel32 = ctypes.windll.kernel32
    kernel32.SetConsoleMode(kernel32.GetStdHandle(-11), 7)

# Helper function to format sets without braces and commas
def format_set(s):
    if not s:
        return ''
    elements = sorted(s)
    return '\n' + '\n'.join('  ' + e for e in elements)

def format_incompatibilities(incs):
    if not incs:
        return ''
    formatted_incs = []
    for inc in incs:
        formatted_inc = '\n'.join('  ' + s for s in sorted(inc))
        formatted_incs.append(formatted_inc)
    return '\n\n'.join(formatted_incs)

def format_inferences(infs):
    if not infs:
        return ''
    formatted_infs = []
    for inf in sorted(infs, key=lambda x: str(x)):
        premises = '\n'.join('  ' + p for p in sorted(inf.premises))
        conclusion = '  |- ' + inf.conclusion
        formatted_infs.append(f"{premises}\n{conclusion}")
    return '\n\n'.join(formatted_infs)

# ANSI color codes
RED = '\033[31m'
GREEN = '\033[32m'
RESET = '\033[0m'

# Define the Inference class
class Inference:
    def __init__(self, premises, conclusion):
        self.premises = frozenset(premises)
        self.conclusion = conclusion

    def __eq__(self, other):
        return self.premises == other.premises and self.conclusion == other.conclusion

    def __hash__(self):
        return hash((self.premises, self.conclusion))

    def __str__(self):
        premises_str = '\n'.join('  ' + p for p in sorted(self.premises))
        return f"{premises_str}\n  |- {self.conclusion}"

    def __repr__(self):
        return str(self)

# Define the Challenge class
class Challenge:
    def __init__(self, target, sentence):
        self.target = target
        self.sentence = sentence

    def __eq__(self, other):
        return self.target == other.target and self.sentence == other.sentence

    def __hash__(self):
        return hash((self.target, self.sentence))

    def __str__(self):
        return f"challenged {self.target.name}'s entitlement to \"{self.sentence}\""

    def __repr__(self):
        return str(self)

# Define the Agent class
class Agent:
    def __init__(self, name,
                 intelligence=100,
                 committive=[[["A is red"], "A is colored"],
                             [["A is blue"], "A is colored"],
                             [["A is green"], "A is colored"]],
                 permissive=[[["A is red", "A is fragrant"], "A is edible"],
                             [["A is blue", "A is small"], "A is poisonous"]],
                 incompatibles=[["A is red", "A is blue"],
                                ["A is red", "A is green"],
                                ["A is blue", "A is green"],
                                ["A is edible", "A is poisonous"]]):
        self.name = name
        self.intelligence = intelligence
        self.commitments_avowed = set()
        self.incompatibilities = [frozenset(inc) for inc in incompatibles]
        self.committive_inferences = {Inference(premises, conclusion)
                                      for premises, conclusion in committive}
        self.permissive_inferences = {Inference(premises, conclusion)
                                      for premises, conclusion in permissive}
        self.challenges_issued = set()

    def __eq__(self, other):
        return isinstance(other, Agent) and self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def asserts(self, sentence):
        self.commitments_avowed.add(sentence)

    def disavows(self, sentence):
        self.commitments_avowed.discard(sentence)

    def challenges(self, agent, sentence):
        if sentence in agent.commitments_avowed:
            self.challenges_issued.add(Challenge(agent, sentence))

    def withdraws_challenge(self, agent, sentence):
        self.challenges_issued.discard(Challenge(agent, sentence))

    def __str__(self):
        return (f"{self.name}\n"
                f"Intelligence = {self.intelligence}\n"
                f"Commitments avowed:{format_set(self.commitments_avowed)}\n"
                f"Sets taken to be incompatible:\n{format_incompatibilities(self.incompatibilities)}\n"
                f"Committive inferences accepted:\n{format_inferences(self.committive_inferences)}\n"
                f"Permissive inferences accepted:\n{format_inferences(self.permissive_inferences)}\n"
                f"Challenges issued:\n{self.challenges_issued}\n")

    def __repr__(self):
        return str(self)

# Define the Game class
class Game:
    def __init__(self):
        self.agents = set()
        self.transcript = deque(maxlen=100)  # Keep only the last 100 entries
        self.previous_score = ""

    def reset(self):
        self.agents.clear()
        self.transcript.clear()
        self.previous_score = ""

    def agent_named(self, name):
        for agent in self.agents:
            if agent.name.lower() == name.lower():
                return agent
        return None

    def assertions_challenged(self, agent):
        challenged_sentences = set()
        for a in self.agents:
            for c in a.challenges_issued:
                if c.target == agent:
                    challenged_sentences.add(c.sentence)
        return challenged_sentences

    def assertions_unchallenged(self, agent):
        return agent.commitments_avowed - self.assertions_challenged(agent)

    def all_unchallenged_assertions(self):
        all_assertions = set()
        for agent in self.agents:
            all_assertions |= self.assertions_unchallenged(agent)
        return all_assertions

    def consequences_once(self, inferences, basis):
        conclusions = set()
        for inference in inferences:
            if inference.premises <= basis:
                conclusions.add(inference.conclusion)
        return basis | conclusions

    def compatible_with(self, incompatibilities, commitments, sentence):
        for inc in incompatibilities:
            if inc <= commitments | {sentence} and not inc <= commitments:
                return False
        return True

    def remove_incompatibles(self, sentences, commitments, incompatibilities):
        return {s for s in sentences if self.compatible_with(incompatibilities, commitments, s)}

    def consequences_once_and_prune(self, inferences, base, commitments, incompatibilities):
        return self.remove_incompatibles(self.consequences_once(inferences, base), commitments, incompatibilities)

    def fixed_point(self, s, times, func):
        if times == 0:
            return s
        else:
            nxt = func(s)
            if s == nxt:
                return s
            else:
                return self.fixed_point(nxt, times - 1, func)

    def commitments(self, scorekeeper, other):
        return self.fixed_point(other.commitments_avowed, scorekeeper.intelligence,
                                lambda s: self.consequences_once(scorekeeper.committive_inferences, s))

    def incompatibles(self, scorekeeper, other):
        coms = self.commitments(scorekeeper, other)
        return {inc for inc in scorekeeper.incompatibilities if inc <= coms}

    def entitlements(self, scorekeeper, other):
        coms = self.commitments(scorekeeper, other)
        incs = scorekeeper.incompatibilities
        times = other.intelligence
        base = self.remove_incompatibles(self.all_unchallenged_assertions(), coms, incs)
        return self.fixed_point(base, times, lambda s: self.expand_entitlements(coms, s, incs,
                                                                                scorekeeper.committive_inferences,
                                                                                scorekeeper.permissive_inferences,
                                                                                times))

    def expand_entitlements(self, coms, ents, incs, cominfs, perminfs, times):
        ents2 = self.consequences_once_and_prune(cominfs, ents, coms, incs)
        ents3 = self.consequences_once_and_prune(perminfs, ents & coms, coms, incs)
        return ents2 | ents3

    def score(self, scorekeeper, other):
        coms = self.commitments(scorekeeper, other)
        ents = self.entitlements(scorekeeper, other)
        incs = self.incompatibles(scorekeeper, other)
        return (f"\n{scorekeeper.name}'s score on {other.name}:\n"
                f"Commitments:{format_set(coms)}\n"
                f"Entitlements:{format_set(ents)}\n"
                f"Incompatibles:\n{format_incompatibilities(incs)}\n")

    def score_all(self):
        agents = sorted(self.agents, key=lambda a: a.name)
        output = ""
        for sk in agents:
            for ot in agents:
                output += self.score(sk, ot)
        return output

    def startup_message(self):
        return (
            "Welcome to the game of giving and asking for reasons,\n"
            "a simulation of the linguistic scorekeeping dynamics\n"
            "described in chapter 3 of Robert Brandom's book\n"
            "Making It Explicit (Harvard University Press, 1994).\n\n"
            "Adapted from Gogar.rb - gogar in ruby (c) 2006 John MacFarlane.\n\n"
            "For a list of sample commands, type help\n\n"
        )

    def help_message(self):
        return (
            "\nlist agents\nadd agent Sal [with intelligence 50]\nremove agent Bob\n"
            "set intelligence of Bob to 50\nnew game\nscore\nBob's score on Ann\n"
            "Bob asserts A is red\nBob disavows A is red\nAnn challenges Bob's entitlement to A is red\n"
            "Ann abandons his challenge to Bob's entitlement to A is red\n"
            "Bob adds committive inference: {A is red; A is small} |- A is dangerous\n"
            "Bob adds incompatibility: {A is red; A is yellow}\n"
            "Ann removes incompatibility: {A is blue; A is red}\n"
            "Ann removes permissive inference: {A is small; A is blue} |- A is edible\n"
            "history\nAnn\nhelp\nquit\n\n"
        )

    def process_command(self, inp):
        inp = inp.strip()
        result = ""
        # Quit or exit
        if re.match(r'^\s*(quit|exit)\s*$', inp):
            result = "Goodbye.\n"
        # Help
        elif re.match(r'^\s*help\s*$', inp):
            result = self.help_message()
        # History
        elif re.match(r'^\s*(history|transcript)\s*$', inp):
            result = '\n'.join(f"> {cmd}\n{resp.strip()}" for cmd, resp in self.transcript)
            result += '\n'
        # List agents
        elif re.match(r'^\s*(list)?\s*agents\s*$', inp):
            result = '\n'.join(str(agent) for agent in self.agents) + '\n'
        # Add agent with optional intelligence
        elif match := re.match(r'^\s*add\s*agent\s+(\w+)(?:\s+with\s+intelligence\s+(\d+))?\s*$', inp):
            name = match.group(1)
            intelligence = int(match.group(2)) if match.group(2) else 100  # default intelligence
            if self.agent_named(name):
                result = f"An agent named {name} already exists.\n"
            else:
                agent = Agent(name, intelligence=intelligence)
                self.agents.add(agent)
                result = f"Agent {name} added with intelligence {intelligence}.\n"
        # Set intelligence of an existing agent
        elif match := re.match(r'^\s*set\s+intelligence\s+of\s+(\w+)\s+to\s+(\d+)\s*$', inp):
            agent_name, intelligence = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                agent.intelligence = int(intelligence)
                result = f"Set intelligence of {agent_name} to {intelligence}.\n"
        # Remove agent
        elif match := re.match(r'^\s*remove\s*agent\s+(\w+)\s*$', inp):
            name = match.group(1)
            agent = self.agent_named(name)
            if agent:
                self.agents.remove(agent)
                result = f"Agent {name} removed.\n"
            else:
                result = f"There is no agent named {name}.\n"
        # New game
        elif re.match(r'^\s*new\s*game\s*$', inp):
            self.reset()
            self.agents.add(Agent("Ann"))
            self.agents.add(Agent("Bob"))
            result = self.startup_message()
        # Score of one agent on another
        elif match := re.match(r'^\s*(\w+)\'s\s+score\s+on\s+(\w+)\s*$', inp):
            scorekeeper_name, other_name = match.groups()
            scorekeeper = self.agent_named(scorekeeper_name)
            other = self.agent_named(other_name)
            if not scorekeeper:
                result = f"Agent {scorekeeper_name} not found. Try: list agents\n"
            elif not other:
                result = f"Agent {other_name} not found. Try: list agents\n"
            else:
                result = self.score(scorekeeper, other)
        # Overall score
        elif re.match(r'^\s*score\s*$', inp):
            current_score = self.score_all()
            result = self.diff_scores(self.previous_score, current_score)
            self.previous_score = current_score
        # Agent asserts a sentence
        elif match := re.match(r'^\s*(\w+)\s+asserts:?\s*(.+)\s*$', inp):
            agent_name, sentence = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                agent.asserts(sentence.strip('"'))
                current_score = self.score_all()
                result = self.diff_scores(self.previous_score, current_score)
                self.previous_score = current_score
        # Agent disavows a sentence
        elif match := re.match(r'^\s*(\w+)\s+disavows:?\s*(.+)\s*$', inp):
            agent_name, sentence = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                sentence = sentence.strip('"')
                if sentence not in agent.commitments_avowed:
                    result = f"Agent {agent_name} has not asserted \"{sentence}\"\n"
                else:
                    agent.disavows(sentence)
                    current_score = self.score_all()
                    result = self.diff_scores(self.previous_score, current_score)
                    self.previous_score = current_score
        # Agent challenges another's entitlement
        elif match := re.match(r'^\s*(\w+)\s+challenges\s+(\w+).*to\s+("?)(.+?)\3\s*$', inp):
            agent_name, target_name, _, sentence = match.groups()
            agent = self.agent_named(agent_name)
            target = self.agent_named(target_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            elif not target:
                result = f"Agent {target_name} not found. Try: list agents\n"
            else:
                if sentence not in target.commitments_avowed:
                    result = f"{target.name} never asserted \"{sentence}\"\n"
                else:
                    agent.challenges(target, sentence)
                    current_score = self.score_all()
                    result = self.diff_scores(self.previous_score, current_score)
                    self.previous_score = current_score
        # Agent withdraws a challenge
        elif match := re.match(r'^\s*(\w+)\s+abandons\s+.*challenge\s+to\s+(\w+).*to\s+("?)(.+?)\3\s*$', inp):
            agent_name, target_name, _, sentence = match.groups()
            agent = self.agent_named(agent_name)
            target = self.agent_named(target_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            elif not target:
                result = f"Agent {target_name} not found. Try: list agents\n"
            else:
                agent.withdraws_challenge(target, sentence)
                current_score = self.score_all()
                result = self.diff_scores(self.previous_score, current_score)
                self.previous_score = current_score
        # Agent adds committive or permissive inference
        elif match := re.match(r'^\s*(\w+)\s+adds\s+(committive|permissive)\s+inference\s*:\s*\{(.+)\}\s*\|-\s*(.+)\s*$', inp):
            agent_name, inf_type, premises_str, conclusion = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                premises = [p.strip() for p in premises_str.split(';')]
                inference = Inference(premises, conclusion.strip())
                if inf_type == 'committive':
                    agent.committive_inferences.add(inference)
                else:
                    agent.permissive_inferences.add(inference)
                current_score = self.score_all()
                result = self.diff_scores(self.previous_score, current_score)
                self.previous_score = current_score
        # Agent removes committive or permissive inference
        elif match := re.match(r'^\s*(\w+)\s+removes\s+(committive|permissive)\s+inference\s*:\s*\{(.+)\}\s*\|-\s*(.+)\s*$', inp):
            agent_name, inf_type, premises_str, conclusion = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                premises = [p.strip() for p in premises_str.split(';')]
                inference = Inference(premises, conclusion.strip())
                if inf_type == 'committive':
                    agent.committive_inferences.discard(inference)
                else:
                    agent.permissive_inferences.discard(inference)
                current_score = self.score_all()
                result = self.diff_scores(self.previous_score, current_score)
                self.previous_score = current_score
        # Agent adds incompatibility
        elif match := re.match(r'^\s*(\w+)\s+adds\s+incompatibility\s*:\s*\{(.+)\}\s*$', inp):
            agent_name, sentences_str = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                sentences = [s.strip() for s in sentences_str.split(';')]
                agent.incompatibilities.append(frozenset(sentences))
                current_score = self.score_all()
                result = self.diff_scores(self.previous_score, current_score)
                self.previous_score = current_score
        # Agent removes incompatibility
        elif match := re.match(r'^\s*(\w+)\s+removes\s+incompatibility\s*:\s*\{(.+)\}\s*$', inp):
            agent_name, sentences_str = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                sentences = [s.strip() for s in sentences_str.split(';')]
                inc_set = frozenset(sentences)
                if inc_set in agent.incompatibilities:
                    agent.incompatibilities.remove(inc_set)
                current_score = self.score_all()
                result = self.diff_scores(self.previous_score, current_score)
                self.previous_score = current_score
        # Display agent's state
        elif match := re.match(r'^\s*(\w+)\s*$', inp):
            agent_name = match.group(1)
            agent = self.agent_named(agent_name)
            if agent:
                result = str(agent)
            else:
                result = "Command not recognized. Try: help\n"
        else:
            result = "Command not recognized. Try: help\n"

        self.transcript.append((inp, result))
        return result

    def diff_scores(self, old, new):
        diff = []
        old_lines = old.splitlines()
        new_lines = new.splitlines()
        diff_lines = difflib.ndiff(old_lines, new_lines)
        for line in diff_lines:
            if line.startswith('+ '):
                diff.append(f"{GREEN}{line[2:]}{RESET}")
            elif line.startswith('- '):
                diff.append(f"{RED}{line[2:]}{RESET}")
            elif line.startswith('  '):
                diff.append(line[2:])
        return '\n'.join(diff) + '\n'

# Main function
def main():
    parser = argparse.ArgumentParser(description='GOGAR -- the game of giving and asking for reasons')
    parser.add_argument('-w', '--web', nargs='?', const=9094, type=int, help='Run web version of GOGAR [on port PORT]')
    args = parser.parse_args()

    if args.web is not None:
        print("Web interface is not implemented in this version.")
    else:
        # Command-line interface
        game = Game()
        game.reset()
        game.agents.add(Agent("Ann"))
        game.agents.add(Agent("Bob"))
        print(game.startup_message())
        # Enable readline history
        readline.parse_and_bind("tab: complete")
        while True:
            try:
                inp = input("GOGAR> ")
                response = game.process_command(inp)
                print(response)
                if response.strip() == "Goodbye.":
                    break
            except (EOFError, KeyboardInterrupt):
                print("\nGoodbye.")
                break

if __name__ == '__main__':
    main()