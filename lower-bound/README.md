# A lower bound C > 2

For the explicit law $p$ defined by the infinite Gaussian sums in [PROOF.md](PROOF.md), with $n=30$ and exact $\alpha=3502021035450561/2^{53}$, the uniform latent $L$ on its 30 translates gives

$$
\frac{T(p)}{\tau(p)}\geq\frac{T(p)}{\tau_L}\geq R>2.0012323023>2.
$$

Thus every universal comparison constant satisfies $C\geq R>2$. Here $R$ is the exact rational printed by [verify.py](verify.py), and $\tau_L$ is the score of the explicitly constructed latent. Only $\tau(p)\leq\tau_L$ is used; optimality of $L$ is not claimed. The sharp value of $C$ is unknown. The ratio is unit-free: converting both errors from nats to bits multiplies them by the same factor.

**Standing: a paper proof with interval-certified numerical inputs and computer-checked cover evidence. This lower bound is outside the Lean development.** The two implementations of the leaf check have separate code and arithmetic, but share the grid, transfer bound, bounding method and proposer search. Historical executions have the identity limitation described below.

The proof, the checking code and these documents were produced with language models under the author's direction, as the repository README's "How this was made" section describes. No statement inherits verification status from that process; the model readings mentioned in section 8 of [PROOF.md](PROOF.md) are not human checks. The author reports that no human has checked these proofs line by line.

## Verification modes

Run [verify.py](verify.py) with Python 3 from this directory, choosing one mode:

- With no option, it hashes every file in `data/` and `check/`, runs the assembly checks over all 912 families including prefix-code coverage, independently recomputes the packing scalar and ratio, and requires the exact $R>2.0012323023$. Failure exits nonzero. This mode does not recompute the per-leaf bounds or the input enclosures.
- `--quick` performs the same checks except that it skips the assembly check of prefix-code coverage. It still reads each leaf file and compares its leaf count. It does not recompute per-leaf bounds or input enclosures.
- `--mutate` checks an unmodified scratch copy, flips one byte of one copied data file, and requires the manifest check to reject exactly that file while the original remains unchanged. It tests byte-integrity detection.
- `--leaves` regenerates proposals and runs [the separate exact checker](check/independent/checker.py) over the selected leaves, failing if any requested leaf remains uncertified. With no `--families`, all 912 families are selected, which is about 68 CPU-hours (see below); start with `--families 0,751,819`. A rejected leaf is retried with a longer search, then with one to three additional split levels. The checker verifies that any split children cover the original leaf. When a whole family is selected, the checker also runs its own prefix-code check on it.

Per-leaf options: `--families` accepts indices, ranges or names, for example `0,10-12,d0_L2`; `--start S --limit N` selects the existing leaves from index $S$ through $S+N-1$ in each selected family. Prefix-code coverage is checked whenever the selected range is the entire family, including when options happen to select that entire range. `--chunk K` controls job size (default 3000); `--workers W` controls concurrent jobs (default 1). An empty overall selection is an error. The verifier and its Python children run at BelowNormal priority on Windows. Generated certificate files are deleted after checking.

What a run does to the machine. `verify.py` never writes into this folder. It writes scratch copies (about 20 MB in all, plus numba's compiled cache in per-leaf mode) to the system temporary directory and removes them when it finishes; a killed run can leave a `c2verify_*`, `c2mutate_*` or `c2leaves_*` directory there. On Windows it refuses to run if it cannot verify BelowNormal priority. Any file under `data/` or `check/` that is not in the manifest, such as a `__pycache__` directory left by importing a module or a `.DS_Store` written by macOS, makes the manifest step fail as EXTRA; delete it and rerun. A run that stops for lack of memory is not a verdict on the bound. The proposer is untrusted in the sense that its output earns no credit; it is ordinary code and runs with your user rights like the rest, and nothing here uses the network.

The proposer reuses the original floating-point search and is untrusted. Acceptance depends on the checker's own reconstruction and exact positive lower bound, or its reconstruction that a node is logically empty. The checker uses only the standard library.

The supplied run logs report:

- Whole families 0, 751 and 819: 609 leaves certified in 93 seconds of leaf work (99 seconds in all).
- Family 884, first 10,000 leaves: 713 seconds of leaf work (718 seconds in all), one worker, minimum margin about $1.0846\cdot10^{-7}$.
- Family 869, leaf 90662: accepted after one split, with minimum child margin about $1.770\cdot10^{-3}$.
- The full run (`receipts/verify-full.log`): total wall time 1192.3 s (19 minutes 52 seconds) and 12.25 GiB peak working set of the assembly step on the author's computer. The quick run (`receipts/verify-quick.log`): 49.5 s and 7.07 GiB. These are measurements, not resource guarantees.

The historical complete replay certified 3,448,987 stored leaves, with five repaired by splitting. The public wrapper has only been tested on the subsets above. Its whole per-leaf run has not been performed. Historical proposer-plus-checker CPU time was 209,694 seconds; extrapolating the measured rate of the public family-884 sample (10,000 leaves in 713.4 s of leaf work, one worker) over 3,448,987 leaves gives about 68 CPU-hours (an extrapolation). Parallel scaling and memory consumption depend on the chosen families and machine.

Requirements: Python 3, tested with 3.14.0 on Windows 10. The manifest, scalar and separate checker use only the standard library. Assembly and proposal generation also require numpy and numba (tested with 2.3.4 and 0.65.1). [law_elementary.py](check/law_elementary.py) uses mpmath (tested with 1.4.1); it is an ordinary 400-digit numerical comparison. [enclose_inputs.py](check/enclose_inputs.py) separately uses directed interval arithmetic to verify the law, positivity, transfer and entropy inputs. Neither is invoked by `verify.py`. Non-Windows execution has not been tested.

## Contents and execution evidence

- [PROOF.md](PROOF.md): definitions, paper reduction, arithmetic checks and limitations.
- `data/law.json`: grid integers with denominator $2^{52}$, probability intervals and entropy/latent-score bounds. The grid is not normalized to one.
- `data/price_v4.json`: windows, cell prices, mass penalties, packing minimum and exact ratio. `data/prices.json` supplies the window specification compared by the assembler. `data/transfer.json` supplies the transfer constants and law enclosures.
- `data/cover/v4/`: 912 family summaries and 912 compressed leaf-path sets. The compressed bytes are retained. (GitHub's web listing of this directory shows only the first 1,000 entries; a clone is complete.)
- `check/refreeze/`: the original assembly module, its imported helpers and the search modules used by the proposer. The directory name is a historical implementation identifier. Only the modules and functions called by the documented modes are a runnable interface; the old search executable requires additional development modules.
- `check/independent/`: the separate exact checker and scalar calculator, plus the untrusted proposer. `driver.py` and `parts.py` preserve the earlier scheduler and rejection-range logic; `verify.py` implements its own scheduling.
- `check/code_upper.py`: interval-arithmetic cost of one explicit deterministic code (X in consecutive blocks of sizes 8, 8, 7, 7), an upper bound on $T(p)$ and so on $T(p)/\tau_L$ (see the last part of section 7 of PROOF.md). It is not an upper bound on $C$ and is not invoked by `verify.py`.
- `check/doc_numbers.py`: prints the relative widths of the stored probability enclosures, the error of the Gaussian-profile fit, the numerator $N$ and the installed library versions that PROOF.md quotes (log in `receipts/doc-numbers.log`). It is not invoked by `verify.py`.
- `check/run_final.py`: runs the assembler over checked scratch copies so generated files do not modify `data/`.
- `data/PROOF.txt`: an archival development note, not the current proof. It discusses obsolete prices and modules absent from this package. Historical uppercase labels and internal development terms in preserved source comments identify the original work; they are not additional hypotheses or inputs. The current proof defines and uses a feasible latent directly.
- `MANIFEST.sha256`: sorted SHA-256 entries for every file in `data/` and `check/`. `.gitattributes` disables line-ending conversion for this folder; this does not prevent deliberate editing.
- `receipts/`: logs of the executions described here, regenerated from the final files. In the logs written by `verify.py`, paths inside this folder are shown relative to it, the interpreter is shown as `python`, and scratch directories as `<scratch>`. Preserved original files, such as `data/PROOF.txt` and some files under `check/refreeze/`, are byte-identical copies from the original runs and may contain the original machine's paths in comments or strings, and their docstrings and comments may refer to development notes and modules that are not included (for example CHECKER.md, SCALAR.md, summarize.py and cert_check.py); none of those is read or needed. PROOF.md is the derivation this package relies on.

Each of the eight `verify.py` logs that reach hashing prints the verifier hash, manifest hash and hashes of all packaged `data/` and `check/` files. The ninth, `leaves-empty-selection.log`, records an option error that exits before any hashing. `enclose-inputs.log` prints the hashes of the script, `law.json` and `transfer.json`. Those hashes match the manifest as regenerated for this revision. `verify.py` checks the current files against the manifest; it does not read or authenticate the historical logs. The separate `law-elementary.log`, `code-upper.log` and `doc-numbers.log` contain numerical output without input or script hashes. Any changed script or manifest requires fresh corresponding execution evidence.

Three negative-test receipts show that bad selections fail: `--families ''` is rejected as an empty selection (`leaves-empty-families.log`), `--limit 0` is rejected as an invalid option (`leaves-empty-selection.log`), and `--start` past the end of a family fails with "no leaves selected" (`leaves-start-past-end.log`).

Historical full-replay receipts identify decompressed leaf/proposal content but do not bind the law, price, transfer or checker used in each execution. Agreement of their inputs with the supplied files for unsampled executions is supported by frozen manifests and final hashes; it remains an inference. New subset logs do not replace execution evidence for the unsampled leaves.

## Prior lower bounds

- Satya Benson's published $C\geq1.960073002187$, in [satchlj/stoch-to-det-lower](https://github.com/satchlj/stoch-to-det-lower), is proved in Lean using `native_decide`; it is not reproduced here. The dual inequality of section 5 of [PROOF.md](PROOF.md), taken without its block-mass penalty, is the price dual his proofs use: `DualValid` and `T_lower_of_dual` in `StochToDet1960/Bound.lean` of that repository (a declaration of the same name is in `StochToDet1948/Bound.lean`), as read at its commit `15ae7dae`. The block-mass penalty, the packing minimum, the cover by symmetry roots and the law are specific to this proof.

The author reports that no human has checked these proofs line by line.
