# Natural latents blueprint

The blueprint is a nested Lake package. Build the root library first, then this package, one Lake process at a time.
From the repository root:

```sh
lake exe cache get
lake build
cd blueprint
lake exe cache get
lake build
bash scripts/ci.sh
```

On Windows, run `python scripts/windows_md4lean.py` in `blueprint/` before its `lake build`. It adds the native DLL
export flag to the cached MD4Lean configuration at its pinned revision; Linux and macOS use the dependency unchanged.

The site is written to `blueprint/_out/site/html-multi/index.html`. Dependency updates belong to this nested package;
the root manifest and toolchain stay fixed. CI builds and checks the blueprint on pushes and pull requests; publishing
it to Pages is a separate, manually dispatched workflow job.
