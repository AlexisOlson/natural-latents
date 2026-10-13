"""Delete declarations outside the headline theorems' dependency closure.

usage: python scripts/prune.py DECLS_TSV [--write]

DECLS_TSV is `closure.decls.tsv` from `scripts/DeclClosure.lean`. Every module under `NaturalLatents/` except
`Statement` and `Main` is processed:
  * a module with no declaration in the closure is deleted, and each importer imports its imports instead;
  * in the other modules, every top-level declaration whose source range is not in the closure is deleted.
Structural commands (namespace, section, end, open, variable, universe, set_option, attribute, notation,
module and section documentation) are kept. Lines are deleted, never edited. Without --write it only reports.
"""
import re
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
KEEP_ALWAYS = {"NaturalLatents.Statement", "NaturalLatents.Main", "NaturalLatents.General"}
DECL_KW = {"theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive", "opaque",
           "example", "irreducible_def", "noncomputable def", "alias"}
MODIFIERS = {"private", "protected", "noncomputable", "partial", "nonrec", "scoped", "local"}
IMP = re.compile(r"^import\s+(\S+)\s*$")


def mod_path(mod):
    return REPO / (mod.replace(".", "/") + ".lean")


def all_modules():
    out = []
    for p in (REPO / "NaturalLatents").rglob("*.lean"):
        m = ".".join(p.relative_to(REPO).with_suffix("").parts)
        if m not in KEEP_ALWAYS:
            out.append(m)
    return sorted(out)


def comment_state(lines):
    """For each line, whether it starts inside a block comment."""
    depth, starts = 0, []
    for line in lines:
        starts.append(depth > 0)
        i = 0
        while i < len(line):
            two = line[i:i + 2]
            if depth == 0 and two == "--":
                break
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/" and depth > 0:
                depth -= 1
                i += 2
            else:
                i += 1
    return starts


def chunks(lines):
    """Split a file into top-level commands: list of (first, last) 0-based line indices."""
    inside = comment_state(lines)
    heads = [i for i, l in enumerate(lines)
             if l[:1] not in ("", " ", "\t", "\n", "\r") and not inside[i] and not l.startswith("--")]
    spans = []
    for k, h in enumerate(heads):
        end = (heads[k + 1] if k + 1 < len(heads) else len(lines)) - 1
        spans.append([h, end])
    # merge a doc comment, attribute line, or `... in` prefix with the command it decorates
    merged, last = [], None
    for s in spans:
        if merged:
            prev = "".join(lines[last[0]:last[1] + 1])
            code = re.sub(r"--[^\n]*", "", prev).rstrip()
            if (lines[last[0]].startswith("/--") or re.fullmatch(r"(@\[[^\]]*\]\s*)+", code)
                    or re.search(r"\bin$", code)):
                merged[-1][1] = s[1]
                last = s
                continue
        merged.append(list(s))
        last = s
    return merged


def strip_prefix(text):
    """Text of a command after its doc comment, attributes and `... in` prefixes."""
    t = text
    while True:
        t0 = t
        t = t.lstrip()
        if t.startswith("/--"):
            t = t[t.index("-/") + 2:]
        elif t.startswith("@["):
            depth, i = 0, 0
            while i < len(t):
                if t[i] == "[":
                    depth += 1
                elif t[i] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            t = t[i + 1:]
        else:
            m = re.match(r"(omit|include|open|set_option|variable)\b[^\n]*?\bin\s*\n", t)
            if m:
                t = t[m.end():]
        if t == t0:
            return t


def keyword(text):
    words = strip_prefix(text).split()
    while words and words[0] in MODIFIERS:
        words = words[1:]
    return words[0] if words else ""


def main():
    tsv = Path(sys.argv[1])
    write = "--write" in sys.argv
    kept = defaultdict(set)
    used_modules = set()
    for row in tsv.read_text(encoding="utf-8").splitlines()[1:]:
        name, mod, start, end = row.split("\t")
        used_modules.add(mod)
        if start:
            kept[mod].update(range(int(start) - 1, int(end)))
    mods = all_modules()
    dead = [m for m in mods if m not in used_modules]
    live = [m for m in mods if m in used_modules]

    imports = {}
    for m in mods + sorted(KEEP_ALWAYS):
        imports[m] = [mm.group(1) for l in mod_path(m).read_text(encoding="utf-8").splitlines()
                      if (mm := IMP.match(l))]

    def resolve(m, seen=()):
        if m not in dead:
            return [m]
        out = []
        for d in imports[m]:
            if d.startswith("NaturalLatents.") and d not in seen:
                out += resolve(d, seen + (m,))
            elif not d.startswith("NaturalLatents."):
                out.append(d)
        return out

    # Candidate drops: declaration chunks outside the closure. A lemma used by `simp` or `rw` as a
    # definitional (rfl) rewrite leaves no constant in the proof term, so any dropped declaration whose
    # name still occurs in kept source is restored, to a fixed point.
    files = {m: mod_path(m).read_text(encoding="utf-8").splitlines(keepends=True) for m in mods}
    cand = {}  # (module, first line) -> (last line, declared short name)
    for m in live:
        lines = files[m]
        for a, b in chunks(lines):
            text = "".join(lines[a:b + 1])
            kw = keyword(text)
            if kw.startswith("#"):
                cand[(m, a)] = (b, None)
            elif kw in DECL_KW and not (set(range(a, b + 1)) & kept[m]):
                rest = strip_prefix(text).split()
                while rest and rest[0] in MODIFIERS:
                    rest = rest[1:]
                name = rest[1].split(".")[-1] if len(rest) > 1 and kw not in ("example", "instance") else None
                cand[(m, a)] = (b, name)
    restored, restored_texts = 0, []
    while True:
        gone = defaultdict(set)
        for (m, a), (b, _) in cand.items():
            gone[m].update(range(a, b + 1))
        kept_text = "".join(l for m in live + sorted(KEEP_ALWAYS)
                            for i, l in enumerate(files.get(m) or mod_path(m).read_text(encoding="utf-8")
                                                  .splitlines(keepends=True))
                            if i not in gone[m])
        # names that a tactic can use without leaving a constant: rewrite and simp lists, unfold, delta
        spots = re.findall(r"\b(?:simp|simpa|simp_all|dsimp|rw|rwa|simp_rw|nth_rw|nth_rewrite|field_simp|"
                           r"norm_num|push_cast|erw|rewrite|simp_arith|positivity|aesop|gcongr|fun_prop)\b"
                           r"[^\[\n]*\[([^\]]*)\]", kept_text)
        spots += re.findall(r"\b(?:unfold|delta)\b([^\n]*)", kept_text)
        spots += restored_texts  # a restored declaration needs everything it names
        tokens = set()
        for spot in spots:
            for tok in re.findall(r"[\w.'!?₀-₉]+", spot):
                tokens.update(tok.split("."))
        back = [k for k, (b, name) in cand.items() if name and name in tokens]
        if not back:
            break
        for k in back:
            m, a = k
            restored_texts.append("".join(files[m][a:cand[k][0] + 1]))
            del cand[k]
        restored += len(back)

    before = after = 0
    report = []
    for m in mods:
        lines = files[m]
        before += len(lines)
        if m in dead:
            report.append((len(lines), 0, m + "  (deleted)"))
            if write:
                mod_path(m).unlink()
            continue
        drop = set()
        for (mm, a), (b, _) in cand.items():
            if mm == m:
                drop.update(range(a, b + 1))
        out = [l for i, l in enumerate(lines) if i not in drop]
        after += len(out)
        report.append((len(lines), len(out), m))
        if write:
            mod_path(m).write_text("".join(out), encoding="utf-8", newline="\n")

    # re-thread imports of deleted modules (in every surviving file, Main included)
    for m in live + sorted(KEEP_ALWAYS):
        new, seen = [], set()
        for d in imports[m]:
            for r in resolve(d):
                if r not in seen:
                    seen.add(r)
                    new.append(r)
        if new != imports[m] and write:
            text = mod_path(m).read_text(encoding="utf-8")
            lines = [l for l in text.splitlines(keepends=True) if not IMP.match(l.rstrip("\r\n"))]
            idx = next(i for i, l in enumerate(lines) if not l.startswith("--"))
            lines[idx:idx] = [f"import {d}\n" for d in new]
            mod_path(m).write_text("".join(lines), encoding="utf-8", newline="\n")

    for b, a, m in sorted(report, key=lambda r: r[1] - r[0]):
        print(f"{b:6d} -> {a:6d}  {m}")
    print(f"total {before} -> {after} lines; {len(dead)} modules deleted; {restored} declarations restored by name")


if __name__ == "__main__":
    main()
