#!/usr/bin/env python3
import subprocess
import re
import sys

def get_build_output():
    """
    Run `lake build`, capturing both stdout and stderr, and return
    the combined text.
    """
    proc = subprocess.run(
        ["lake", "build"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    return proc.stdout + proc.stderr

def parse_unsolved_goals(output):
    """
    Scan the build output for lines containing "unsolved goals",
    then collect the following non-error lines as one block per occurrence.
    Returns a list of lists of lines.
    """
    lines = output.splitlines()
    blocks = []
    i = 0
    while i < len(lines):
        # look for the marker
        if "unsolved goals" in lines[i]:
            block = []
            i += 1
            # collect everything until the next "error:" or until blank/error
            while i < len(lines) and not lines[i].startswith("error:"):
                if lines[i].strip():
                    block.append(lines[i])
                i += 1
            blocks.append(block)
        else:
            i += 1
    return blocks

def main():
    out = get_build_output()
    goals = parse_unsolved_goals(out)
    if not goals:
        print("✅ No unsolved-goals blocks found.")
        sys.exit(0)
    for idx, block in enumerate(goals, start=1):
        print(f"\n--- Unsolved goals block #{idx} ---")
        for line in block:
            print(line)
    sys.exit(1)

if __name__ == "__main__":
    main()

