#!/usr/bin/env python3
# gogar.py - GOGAR in Python
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
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import parse_qs
import threading

# Helper function to wrap text for display
def wrap(text, indent="  ", width=78):
    lines = []
    line = ''
    for word in text.split():
        if len(line) + len(word) + 1 > width:
            lines.append(line)
            line = indent + word
        else:
            line += (' ' if line else '') + word
    if line:
        lines.append(line)
    return '\n'.join(lines)

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
        premises_str = ', '.join(self.premises)
        return f"{{{premises_str}}} |- {self.conclusion}"

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

# Define the Agent class
class Agent:
    def __init__(self, name,
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
        self.intelligence = 100
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
                f"{wrap(f'Commitments avowed: {self.commitments_avowed}')}\n"
                f"{wrap(f'Sets taken to be incompatible: {self.incompatibilities}')}\n"
                f"{wrap(f'Committive inferences accepted: {self.committive_inferences}')}\n"
                f"{wrap(f'Permissive inferences accepted: {self.permissive_inferences}')}\n"
                f"{wrap(f'Challenges issued: {self.challenges_issued}')}\n")

# Define the Game class
class Game:
    def __init__(self):
        self.agents = set()
        self.transcript = deque(maxlen=100)  # Keep only the last 100 entries

    def reset(self):
        self.agents.clear()
        self.transcript.clear()

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
        return (f"\nCommitments:  {coms}\n"
                f"Entitlements: {ents}\n"
                f"Incompatibles: {incs}\n\n")

    def score_all(self):
        agents = sorted(self.agents, key=lambda a: a.name)
        output = ""
        for sk in agents:
            for ot in agents:
                output += f"{sk.name}'s score on {ot.name}:" + self.score(sk, ot)
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
            "\nlist agents\nadd agent Sal\nremove agent Bob\nnew game\nscore\nBob's score on Ann\n"
            "Bob asserts A is red\nBob disavows A is red\nAnn challenges Bob's entitlement to A is red\n"
            "Ann abandons his challenge to Bob's entitlement to A is red\n"
            "Bob adds committive inference: {A is red; A is small} |- A is dangerous\n"
            "Bob adds incompatibility: {A is red; A is yellow}\n"
            "Ann removes incompatibility: {A is blue; A is red}\n"
            "Ann removes permissive inference: {A is small; A is blue} |- A is edible\n"
            "Ann\nhelp\nquit\n\n"
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
        # List agents
        elif re.match(r'^\s*(list)?\s*agents\s*$', inp):
            result = '\n'.join(str(agent) for agent in self.agents) + '\n'
        # Add agent
        elif match := re.match(r'^\s*add\s*agent\s+(\w+)\s*$', inp):
            name = match.group(1)
            if self.agent_named(name):
                result = f"An agent named {name} already exists.\n"
            else:
                self.agents.add(Agent(name))
                result = f"Agent {name} added.\n"
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
            result = self.score_all()
        # Agent asserts a sentence
        elif match := re.match(r'^\s*(\w+)\s+asserts\s*:\s*(.+)\s*$', inp):
            agent_name, sentence = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                agent.asserts(sentence.strip('"'))
                result = self.score_all()
        # Agent disavows a sentence
        elif match := re.match(r'^\s*(\w+)\s+disavows\s*:\s*(.+)\s*$', inp):
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
                    result = self.score_all()
        # Agent challenges another's entitlement
        elif match := re.match(r'^\s*(\w+)\s+challenges\s+(\w+)\s+.*\s+"(.+)"\s*$', inp):
            agent_name, target_name, sentence = match.groups()
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
                    result = self.score_all()
        # Agent withdraws a challenge
        elif match := re.match(r'^\s*(\w+)\s+withdraws\s+.*\s+(\w+)\s+.*\s+"(.+)"\s*$', inp):
            agent_name, target_name, sentence = match.groups()
            agent = self.agent_named(agent_name)
            target = self.agent_named(target_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            elif not target:
                result = f"Agent {target_name} not found. Try: list agents\n"
            else:
                agent.withdraws_challenge(target, sentence)
                result = self.score_all()
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
                result = self.score_all()
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
                result = self.score_all()
        # Agent adds incompatibility
        elif match := re.match(r'^\s*(\w+)\s+adds\s+incompatibility\s*:\s*\{(.+)\}\s*$', inp):
            agent_name, sentences_str = match.groups()
            agent = self.agent_named(agent_name)
            if not agent:
                result = f"Agent {agent_name} not found. Try: list agents\n"
            else:
                sentences = [s.strip() for s in sentences_str.split(';')]
                agent.incompatibilities.append(frozenset(sentences))
                result = self.score_all()
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
                result = self.score_all()
        # Display agent's state
        elif match := re.match(r'^\s*(\w+)\s*$', inp):
            agent_name = match.group(1)
            agent = self.agent_named(agent_name)
            if agent:
                result = str(agent) + self.score(agent, agent)
            else:
                result = "Command not recognized. Try: help\n"
        else:
            result = "Command not recognized. Try: help\n"

        self.transcript.append((inp, result))
        return result

# Web server request handler
class GogarHandler(BaseHTTPRequestHandler):
    game = Game()

    def do_GET(self):
        if self.path == '/':
            self.send_response(200)
            self.end_headers()
            response = self.game.startup_message()
            self.wfile.write(response.encode('utf-8'))
        elif self.path.startswith('/transcript'):
            self.send_response(200)
            self.end_headers()
            transcript = '\n'.join(f"> {cmd}\n{resp}" for cmd, resp in self.game.transcript)
            self.wfile.write(transcript.encode('utf-8'))
        else:
            self.send_error(404)

    def do_POST(self):
        length = int(self.headers.get('Content-Length', 0))
        post_data = self.rfile.read(length)
        params = parse_qs(post_data.decode('utf-8'))
        command = params.get('command', [''])[0]
        response = self.game.process_command(command)
        self.send_response(200)
        self.end_headers()
        self.wfile.write(response.encode('utf-8'))

def run_web_server(port):
    server_address = ('', port)
    httpd = HTTPServer(server_address, GogarHandler)
    print(f"Starting web server on port {port}...")
    httpd.serve_forever()

# Main function
def main():
    parser = argparse.ArgumentParser(description='GOGAR -- the game of giving and asking for reasons')
    parser.add_argument('-w', '--web', nargs='?', const=9094, type=int, help='Run web version of GOGAR [on port PORT]')
    args = parser.parse_args()

    if args.web is not None:
        # Start the web server
        web_thread = threading.Thread(target=run_web_server, args=(args.web,))
        web_thread.daemon = True
        web_thread.start()
        try:
            while True:
                pass  # Keep the main thread alive
        except KeyboardInterrupt:
            print("Shutting down web server...")
            sys.exit(0)
    else:
        # Command-line interface
        game = Game()
        print(game.startup_message())
        while True:
            try:
                inp = input("GOGAR> ")
                response = game.process_command(inp)
                print(response)
                if response == "Goodbye.\n":
                    break
            except (EOFError, KeyboardInterrupt):
                print("\nGoodbye.")
                break

if __name__ == '__main__':
    main()
