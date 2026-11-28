# Squeeze screenshots into the smallest PNG

[![make.fun](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/c/png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/gelaspec/png-squeeze-01-run-20261127/rank.svg)](https://make.fun/c/png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/gelaspec/png-squeeze-01-run-20261127/reward.svg)](https://make.fun/c/png-squeeze-01-run-20261127)

A lossless PNG compressor for make.fun's `png-squeeze-01-run-20261127`
bounty: `main.ts` reads each 1280x720 screenshot from `/input/<id>/image.png`
and writes the smallest byte-exact PNG it can to `/output/<id>/image.png`,
inside 60 s for the whole set of eight.

How it works, per image:

1. Decode the stored RGBA PNG and analyse it (opaque / grey / at most 256
   colours / one transparent key), then build the candidate forms: palette
   (by count and by luminance), grey / grey+alpha, RGB / RGBA, with tRNS
   where a single transparent value can replace the alpha channel.
2. Screen the forms and per-row filter choices (None / Sub / Up / Average /
   Paeth, least-signed-sum and fewest-pairs heuristics, plus per-row brute
   force for the best forms) with zlib level 6, keeping the smallest.
3. Compress the winner's filtered bytes with an optimal-parsing deflate in
   the manner of zopfli: a lazy greedy pass for statistics, an entropy cost
   model, then two dynamic-programming parses (the second replays the first
   run's longest-match results from a cache, so it costs almost no match
   finding), length-limited Huffman codes by package-merge, adaptive block
   splitting, and dynamic vs fixed Huffman per block, keeping the smaller.
4. Write the PNG with only IHDR / PLTE / tRNS / IDAT / IEND.

Deterministic by construction: no clock, no randomness, no environment
reads; the work per image is fixed by its bytes, never by wall time.
Node 22, standard library only.

## Check it

From the unpacked kit directory:

```sh
node cli/makefun.mjs grade-local --kit . --bot <repository> --driver process
```

Practice set (local, kit checker): **743,481** of 1,000,000, all 8 instances
byte-exact (house baseline fixed-paeth: 420,399). Per instance: i001 773.1,
i002 742.4, i003 715.7, i004 743.6, i005 804.0, i006 715.7, i007 719.4,
i008 733.8. Full-set runtime ~40 s, peak RSS ~394 MB on this machine.

v2 (29 Nov): sped up from ~52 s to ~40 s after the first submission was
rejected on the server for exceeding the 60 s grade-run budget. The match
search is now two-tier (a short pass, extended only when no decent match
turned up), the screen drops the fixed filters that never win, RGB/RGBA
skip the second DP pass, and RGBA skips per-row brute forcing. The score
cost of those cuts is ~5,400 points (748,882 -> 743,481).
