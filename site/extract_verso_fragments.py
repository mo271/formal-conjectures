#!/usr/bin/env python3
"""
Extract Verso fragments from literate HTML output.

Scans the Verso literate HTML to produce a JSON file with:
- moduleDocs: module path -> rendered module docstring HTML
- constLinks: Lean constant name -> { url, anchor }

Usage: python3 extract_verso_fragments.py <literate-html-dir> <output-json>
"""

import json
import os
import re
import sys


def walk_html_files(root):
    """Find all index.html files under root."""
    for dirpath, _, filenames in os.walk(root):
        for f in filenames:
            if f == 'index.html':
                yield os.path.join(dirpath, f)


def extract_from_html(html_path, base_dir):
    """Extract module doc and const bindings from a single Verso HTML file."""
    with open(html_path, encoding='utf-8') as f:
        html = f.read()

    # Module path relative to base
    rel = os.path.relpath(os.path.dirname(html_path), base_dir)
    module_path = '/' + rel.replace(os.sep, '/') + '/'

    # 1. Module docstring: <div class="... mod-doc ..." ...>CONTENT</div>
    mod_doc_match = re.search(
        r'<div[^>]*class="[^"]*mod-doc[^"]*"[^>]*>([\s\S]*?)</div>',
        html
    )
    module_doc = mod_doc_match.group(1).strip() if mod_doc_match else None

    # 2. Constant bindings: data-binding="const-XXX" ... id="YYY"
    const_map = {}
    for m in re.finditer(r'data-binding="const-([^"]+)"[^>]*id="([^"]+)"', html):
        lean_name = m.group(1)
        verso_id = m.group(2)
        const_map[lean_name] = {
            'url': module_path + '#' + verso_id,
            'anchor': verso_id,
        }

    return module_path, module_doc, const_map


def main():
    if len(sys.argv) < 3:
        print('Usage: python3 extract_verso_fragments.py <literate-html-dir> <output-json>',
              file=sys.stderr)
        sys.exit(1)

    input_dir, output_json = sys.argv[1], sys.argv[2]

    if not os.path.isdir(input_dir):
        print(f'  Warning: {input_dir} not found, writing empty fragments.', file=sys.stderr)
        with open(output_json, 'w') as f:
            json.dump({'moduleDocs': {}, 'constLinks': {}}, f)
        return

    html_files = list(walk_html_files(input_dir))
    print(f'  Scanning {len(html_files)} Verso HTML files...')

    module_docs = {}
    const_links = {}

    for html_file in html_files:
        module_path, module_doc, const_map = extract_from_html(html_file, input_dir)
        if module_doc:
            module_docs[module_path] = module_doc
        const_links.update(const_map)

    output = {'moduleDocs': module_docs, 'constLinks': const_links}
    with open(output_json, 'w') as f:
        json.dump(output, f)

    print(f'  Extracted {len(module_docs)} module docstrings, {len(const_links)} constant links.')


if __name__ == '__main__':
    main()
