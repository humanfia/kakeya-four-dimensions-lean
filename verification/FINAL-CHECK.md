# OpenAI batch 074: final check (combined record)

Problem `oai_074_kakeya_four_dimensions`. Tree `g-oai-074` (state `ended:proved`). Judged commit E
`71391e12db6f5956b54bcdb01a6b1ceeba11604d` (the LOT export of X `e18a9d88893ffcab5d04f3eaea93f240c663a088`,
how=`lot`; v10wz-inlined). Nothing was submitted anywhere.

The final check ran twice, both times with `prep/run/final-oai.py` on copies of the workspace (the real
workspace was unchanged before and after both runs). The full generated reports are kept next to this file:

- run 1: `FINAL-CHECK.run1-20261022T204822Z.md` (`final-oai.py 074 all`, run directory `20261022T204822Z/`);
- run 2: `FINAL-CHECK.run2-20261023T052251Z.md` (`final-oai.py 074 --checker v10wz checkers`, run directory
  `20261023T052251Z/`), which re-ran only the check that run 1 could not finish.

## Verdicts

| Check | Run | Verdict | Time | Log |
|---|---|---|---|---|
| plain `trusted/oai_074_kakeya_four_dimensions` (nanoda forced on for the root) | 1 | **ACCEPTED** | 8971.0 s | `20261022T204822Z/check-plain/check.log` |
| independent recompile + byte compare + `#print axioms` | 1 | **PASS** | build 9720.5 s | `20261022T204822Z/recompile/build.log` |
| `trusted-v10wz` root check + official `trusted-v10` on the same files | 1 | ERROR (infrastructure) | 11660.9 s | `20261022T204822Z/check-v10wz/official.log` |
| `trusted-v10wz` root check + official `trusted-v10` on the same files | 2 | **ACCEPTED** (both) | 17265.5 s | `20261023T052251Z/check-v10wz/check.log`, `official.log` |

**Overall: VERIFIED.** Every checker accepted E, the independent recompile passed, and the only axioms are
`[propext, Classical.choice, Quot.sound]`.

### Run 1's ERROR was not a verdict on E

In run 1 the v10wz check itself accepted ("Lean default kernel accepts the solution", "nanoda kernel accepts the
solution", "Your solution is okay!", `oom_kill 0`). The official `trusted-v10` container that runs after it then
died while building, at module 12608/12684: `error waiting for container: unexpected EOF` at 00:03:19Z, docker
run exit 125. That is the host's dockerd crashing, not the check: `journalctl -u docker` shows a Go panic at
00:03:18Z in swarmkit's raft snapshot transport (`splitSnapshotData`: slice bounds out of range), and systemd
restarted dockerd at 00:04:02Z (`NRestarts=1`). Because the
verdict needs both containers, final-oai.py recorded ERROR. Run 2 repeated exactly this check (same E, same two
trusted directories) and both containers accepted.

## Details that hold for both runs

- **Kernels.** Every checker log shows `Running nanoda kernel on solution` / `nanoda kernel accepts the solution`
  and the Lean default kernel accepting. Each check ran in a fresh container (`deuring-runner:1`, 16 CPUs,
  64g, `--network none`, read-only Lean set).
- **v10wz.** E is LOT's v10wz-inlined export: `trusted-v10wz/<problem>/check.sh root` inlines the WZ package again
  and refuses any byte of E's copy that differs from the package's. The plain `trusted-v10` then judges the same
  files in its own container.
- **Axioms** (run 1 recompile, `import Solution`):
  `'kakeya_four_dimensions' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Statement files.** `Challenge.lean` (`bf8e140c5a8b3516…`) and `ChallengeDeps.lean` (`c1a46df9350eee8b…`) are
  byte-identical in the starter, E, both trusted `pristine.tar`s and the recompile directory. All 12 protected
  files of E match `trusted/<problem>/protected.sha256`.
- **Size.** E has 10,641 files; the submission is 10,625 Lean modules, 1,381,639 lines, 77.4 MB (top-level
  `Submission/` directories Lib, Obl, Seed, WZ). The submission tarball is 17.53 MB gz.
- **Memory.** Container memory.peak was 64.0 GiB (the container limit) in the plain and v10wz checks of both
  runs, with `oom_kill 0`; the recompile peaked at 39.98 GiB. This matters for any benchmark with a lower memory
  limit (Lean-Eval: 16 GB), not for the verdict.
- **Sealed deps.** The deps `.git/index` digest was **7f64b9cb** before and after both runs and in every
  container; the wzlib Lean set's digest was **b7c369c1** before and after.

## Commands

```bash
python3 -I /home/ubuntu/aopt/work/oai-next4/prep/run/final-oai.py 074 all                      # run 1
python3 -I /home/ubuntu/aopt/work/oai-next4/prep/run/final-oai.py 074 --checker v10wz checkers # run 2
```
