# Source provenance

The current Lean source hashes, dependency pins and release artifact hashes are
recorded in [`lean/SOURCE_MANIFEST.json`](../lean/SOURCE_MANIFEST.json).
The dated records in `lean/verification/` identify the exact source snapshots,
declarations and compiler logs they audit. `lean/ReleaseCheck.lean` lists the
release endpoints. See [`BUILD.txt`](../BUILD.txt) for the kernel-checking commands.

The five standalone writeups are distributed as PDFs in `pdf/`.
Their source and PDF hashes are recorded in
`RELEASE_DOCUMENTS_TITLE_CITATIONS_20261105.json`.
Each PDF credits Andrew R. Booker, Min Lee and Nina Zubrilina and carries the
attribution “Written by GPT-6 Astra”.

`source_imports.json` records the imported numerical sources and the original
source and document snapshots. [`VALIDATION.md`](VALIDATION.md) records the
checks performed for that dated export. The C export changes normalize local
include paths and the corresponding compilation comment; no C algorithm was
altered.

The table parameters were reconciled with the publication table. N=79,83,89
use the current two-prime CRT solver; N=38 uses FLINT. N=97 retains the
distributed one-prime CRT/block-Wiedemann pipeline and its pinned CADO revision.
The N=97-only Hall utility is taken from the 64-bit production bundle, not
the older same-named 32-bit utility. The exhaustive minimality scanner is
the newer general-u64 implementation with simultaneous row pruning.
Large production computations are not automatically rerun during packaging.
