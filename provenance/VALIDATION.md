# Export validation — 22 September 2026

- All 305 files in `lean/` match the previously verified source-only export
  byte for byte. The pinned compiler/dependency plan validates all 291 Lean
  modules. That export's independent fresh rebuild and standard-axiom checks
  are included in `lean/verification/`; no fresh second full rebuild was
  needed for identical files.
- All 13 numerical executables compile with GCC 13.3.0, FLINT 3.1.0,
  OpenMP, `-O3 -march=native`, with no compiler warnings in this build.
- The regression suite passes direct F₂, both one-prime CRT variants,
  composite CRT, two-prime CRT, and exact FLINT endpoint checks. At N=38,
  Q=1596, FLINT gives full rational rank while the F₂ defect is 2.
- Small exhaustive minimality scans for N=5 and N=38 pass. The 76 table
  entries and minimality targets match the publication table; all admissible
  N≤95 are present, and N=97 is separately included without minimality.
- N=97's Hall screen, sparse dimensions and large-Q finisher setup pass
  without allocating its production matrix. This catches truncated-modulus
  command-line paths as well as mismatched helper versions.
- The pinned CADO-NFS GF(2) target builds from source with the included
  recipe, serially and under a 4 GiB address-space bound. Its generated
  driver passes the platform/setup check.
- The optional sparse test passes end to end at N=31, Q=10416. The square
  matrix has dimension 171; the determinant-degree rank lower bound is 164
  and the verified independent kernel has dimension 7, certifying completeness.
  The projected finisher gives `final_defect=0`, `assisted_rank=10416/10416`.
  No independent dense elimination is needed for this certificate.
- Both writeups compile with resolved references, no LaTeX warnings
  and no overfull boxes. The distributed PDFs (6 and 15 pages) were visually
  inspected on every page. They replace the TeX sources in this repository.
  All distributed shell scripts pass syntax checks.
- No large production run, complete 76-level minimality scan, or Slurm
  submission was performed while packaging. The optional N=71 distributed
  regression job was not resubmitted.

The imported Lean source and compiler transcript retain their original
whitespace so their recorded hashes remain valid. Generated executables,
matrices and local build products are excluded from Git.
