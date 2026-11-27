# Proof contributions for Google DeepMind Formal Conjectures

Two existing declarations match published Descartes-number results. This folder pairs each theorem with its external proof and the proposed upstream change.

| Declaration | Exact upstream source | Local contribution |
| --- | --- | --- |
| Tóth’s bound, $m>10^{12}$ for every other factorization | [Lines 152–155, including the placeholder](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/DescartesNumber.lean#L152-L155) | [Proof bridge](toth/Check.lean), [existing-proof patch](toth/formal-conjectures.patch), [contributor notes](toth/issue-and-pr.md). The [proof and certificate](https://github.com/Rob1Ham/odd_perfect_number/blob/841bbce6a93f3b79aac04bb79f845a878057d124/OddPerfect/TothTrillion.lean#L23-L29) already have a public immutable revision. |
| Cube-free uniqueness below seven distinct primes | [Lines 161–164, including the placeholder](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/DescartesNumber.lean#L161-L164) | [External theorem](cube-free/CubeFree.lean) and [proof breakdown and contribution proposal](cube-free/proposal.md). The public revision for the new proof and its supporting classification, then a Palomar entry, are prerequisites for its standard upstream reference. |

Download the [Tóth proof package](packages/toth.zip) or the [cube-free proof package](packages/cube-free.zip). Each ZIP contains an entire source project.

The [registry exporter](palomar/prepare.py) creates one standalone Lake project per result, with its pinned dependencies, a Mathlib-only challenge, a separate proof, Comparator configuration, and a metadata template. In each export the challenge intentionally contains a proof hole. The independently compiled solution supplies the proof.

The same upstream Descartes source lists [unrestricted Descartes uniqueness on lines 168–170](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/DescartesNumber.lean#L166-L170) as research open. See [the other targets](partial/README.md) for the exact restricted conclusions and [the MathOverflow notes](mathoverflow-310919/answer-notes.md) for the separate Chen–Luo contribution.

## Checking both sides

The upstream pin is `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8` (Lean 4.33.1). Its [build job](https://github.com/google-deepmind/formal-conjectures/actions/runs/45852403011/job/140021883236) passed the “Build problems” step. DeepMind’s [compiled, interactive source page](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/Wikipedia/DescartesNumber/) also shows the goal immediately before each admission. Lean accepts an admitted proof with a warning. In an upstream checkout at that commit, run the following, substituting the absolute path to this folder for `$packet`.

```bash
lake exe cache get
lake --wfail build FormalConjectures.Wikipedia.DescartesNumber
lake env lean "$packet/UpstreamAxioms.lean"
```

Each of the three printed catalog declarations has a literal `sorry` body. The axiom to look for is `sorryAx`. A proof-reference patch adds metadata and keeps the upstream placeholder, following DeepMind’s policy for long proofs.

In this project at its own Lean 4.36.0 pin, run the following from the repository root. The script builds dependencies, checks the five cube-free modules, both comparison statements, the MathOverflow theorems and the restricted results. It rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Use `--cached` only with existing build artifacts matching the current source.

```bash
bash submissions/formal-conjectures/verify.sh
```

## Verification on this checkout

Both exported projects passed their default `lake build` on Lean 4.36.0 using the available build caches. The local submission check reported the three standard axioms across all 13 audited declarations. Both ZIPs were read back and their Lean sources, Lake configuration, manifest and Comparator configuration compared byte-for-byte with the tested exports. The Tóth patch applied to the pinned DeepMind source and produced precisely the intended annotation change.

The published DeepMind CI result above covers the original upstream commit. The patched upstream module still needs the scoped Lean 4.33.1 build. The exported Solution declarations each printed only the three standard axioms. The attempted Palomar Comparator run requires Linux namespaces for Bubblewrap and stopped on this macOS host before certificate validation. The publisher still needs to confirm authorship, review and licensing in each registry submission.

## Preparing a pull request

1. Check the contributor’s [Google CLA](https://cla.developers.google.com/). Use an existing relevant issue or [open an issue](https://github.com/google-deepmind/formal-conjectures/issues/new) in your own words. The two proposal files are AI-assisted background notes. DeepMind adopts [Mathlib’s AI conventions](https://leanprover-community.github.io/contribute/index.html#use-of-ai), which require human-written GitHub comments and disclosure of how AI contributed in the PR description. Create a branch in a fork of Formal Conjectures.
2. For Tóth, use the linked public proof. The included patch uses the documented single-declaration exception for existing formalizations. To use a published Palomar entry for either theorem, see [registry preparation](palomar/README.md). The generator requires an actual entry URL. Verify its statement and proof revision before using it.
3. In the upstream checkout, apply one proof reference per proposed change. The Tóth patch targets the exact upstream revision above.

```bash
git apply --check "$packet/toth/formal-conjectures.patch"
git apply "$packet/toth/formal-conjectures.patch"
# Alternative after registration, for either target:
# python3 "$packet/proof-reference.py" . cube-free "$entry_url" > /tmp/cube-free.patch
# git apply --check /tmp/cube-free.patch && git apply /tmp/cube-free.patch
lake --wfail build FormalConjectures.Wikipedia.DescartesNumber
```

4. The upstream [agent instructions](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/AGENTS.md) specify a scoped local build with warnings as errors for a problem-file change. Upstream CI runs its project checks. Verify the external links and the declaration’s type and axioms. Link the issue in the PR, credit the published mathematics, and describe the build results and the role of AI accurately. No registry identifier, Google CLA attestation, or upstream approval is assumed by these drafts.

[Upstream proof policy](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/PROOFS.md) · [Contribution and proof-reference rules](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/CONTRIBUTING.md)
