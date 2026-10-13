"""Make generated source locations portable before publishing the site."""

import html
import json
from pathlib import Path, PurePath


def public_source_text(text: str, sources: list[PurePath], repository: PurePath) -> str:
    for source in sources:
        relative = source.relative_to(repository).as_posix()
        for absolute in {str(source), source.as_posix()}:
            # JSON metadata is also embedded in the generated find page.
            variants = {absolute}
            for _ in range(3):
                absolute = json.dumps(absolute, ensure_ascii=False)[1:-1]
                variants.add(absolute)
            variants |= {html.escape(value, quote=True) for value in variants}
            for value in sorted(variants, key=len, reverse=True):
                text = text.replace(value, relative)
    return text


def main() -> None:
    package = Path(__file__).resolve().parents[1]
    repository = package.parent
    sources = list(package.glob('*.lean')) + list((package / 'Chapters').glob('*.lean'))
    site = package / '_out' / 'site' / 'html-multi'
    for relative in ('xref.json', 'find/index.html', '-verso-data/blueprint-manifest.json'):
        path = site / relative
        original = path.read_text(encoding='utf-8')
        public = public_source_text(original, sources, repository)
        if public != original:
            path.write_text(public, encoding='utf-8', newline='\n')
        print(f'Public source locations: {relative}')


if __name__ == '__main__':
    main()
