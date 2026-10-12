# Natural Latents

A Lean 4 proof, depending on Mathlib only, that a stochastic natural latent can be replaced by a deterministic one
at a constant factor below seven.

The two theorems are stated in [NaturalLatents/Statement.lean](NaturalLatents/Statement.lean) and proved in
[NaturalLatents/Main.lean](NaturalLatents/Main.lean).

**Work in progress.** This README is a placeholder. The proof pages, the acknowledgments and the verification guide
come later.

## Verify

```sh
lake exe cache get
lake build
lake env lean -DrelaxedAutoImplicit=false Verify.lean
python3 scripts/check_statement.py
```

The audit passes when the last two commands exit with code 0 and print nothing.

## Credit

Adapted in part from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) (Apache-2.0), including its pull
request #6 by Jeremy Gillen; see [NOTICE](NOTICE).
