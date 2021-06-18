#!/usr/bin/env python3

# One-liner expression:
# [int(''.join(p)) for p in __import__('itertools').permutations('123456789') if all(int(''.join(p[:x]))%x==0 for x in range(1,10))][0]

print(
  # split up for readability
  [
    int(''.join(p))
    for p in
    __import__('itertools').permutations('123456789')
    if all(
      int(''.join(p[:x])) % x == 0
      for x in range(1, 10)
    )
  ][0]
)
