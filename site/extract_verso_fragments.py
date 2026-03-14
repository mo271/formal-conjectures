#!/usr/bin/env python3
"""
Extract Verso fragments from literate HTML output.

Produces a compact JSON with:
- moduleDocs: module path -> rendered module docstring HTML
- constLinks: Lean const name -> { url, anchor, docHtml }

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


def find_enclosing_code_block(html, pos):
    """Find the <code class="hl lean block"> that encloses position `pos`.

    Walks backwards to find the nearest <code class="hl lean" start,
    then uses balanced tag matching to find the correct </code>.
    """
    # Find all <code class="hl lean" starts before pos
    all_starts = [m.start() for m in re.finditer(r'<code class="hl lean', html[:pos])]
    if not all_starts:
        return None

    block_start = all_starts[-1]
    tag_end = html.find('>', block_start) + 1

    # Balanced matching for nested <code>...</code>
    depth = 1
    idx = tag_end
    while depth > 0 and idx < len(html):
        open_pos = html.find('<code', idx)
        close_pos = html.find('</code>', idx)
        if close_pos == -1:
            break
        if open_pos != -1 and open_pos < close_pos:
            depth += 1
            idx = open_pos + 5
        else:
            depth -= 1
            if depth == 0:
                return html[block_start:close_pos + len('</code>')]
            idx = close_pos + 7

    return None


def extract_from_html(html_path, base_dir):
    """Extract module doc and const links from a Verso HTML file."""
    with open(html_path, encoding='utf-8') as f:
        html = f.read()

    rel = os.path.relpath(os.path.dirname(html_path), base_dir)
    module_path = '/' + rel.replace(os.sep, '/') + '/'

    # 1. Module docstring
    mod_doc_match = re.search(
        r'<div[^>]*class="[^"]*mod-doc[^"]*"[^>]*>([\s\S]*?)</div>',
        html
    )
    module_doc = mod_doc_match.group(1).strip() if mod_doc_match else None

    # 2. Find ALL const bindings with id (defining sites) in the entire file
    const_map = {}
    for m in re.finditer(
        r'data-binding="const-([^"]+)"[^>]*id="([^"]+)"', html
    ):
        lean_name = m.group(1)
        verso_id = m.group(2)

        # Find preceding docstring: look back from the enclosing code block
        # for a <div class="md-text"> element, but only up to the previous
        # </code> boundary to avoid grabbing docstrings from earlier defs.
        code_block_start_candidates = [
            cm.start() for cm in re.finditer(r'<code class="hl lean', html[:m.start()])
        ]
        doc_html = None
        if code_block_start_candidates:
            block_start = code_block_start_candidates[-1]
            # Find the end of the previous code block (nearest </code> before this block)
            prev_code_end = html.rfind('</code>', 0, block_start)
            region_start = (prev_code_end + len('</code>')) if prev_code_end >= 0 else max(0, block_start - 3000)
            before_region = html[region_start:block_start]
            doc_matches = list(re.finditer(
                r'<div class="md-text"[^>]*>([\s\S]*?)</div>\s*$',
                before_region
            ))
            if doc_matches:
                doc_html = doc_matches[-1].group(1).strip()

        entry = {
            'url': module_path + '#' + verso_id,
            'anchor': verso_id,
        }
        if doc_html:
            entry['docHtml'] = doc_html
        const_map[lean_name] = entry

    return module_path, module_doc, const_map


def main():
    if len(sys.argv) < 3:
        print('Usage: python3 extract_verso_fragments.py <literate-html-dir> <output-json>',
              file=sys.stderr)
        sys.exit(1)

    input_dir, output_json = sys.argv[1], sys.argv[2]

    if not os.path.isdir(input_dir):
        print(f'  Warning: {input_dir} not found, writing empty fragments.', file=sys.stderr)
        os.makedirs(os.path.dirname(output_json), exist_ok=True)
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

    output = {
        'moduleDocs': module_docs,
        'constLinks': const_links,
    }
    os.makedirs(os.path.dirname(output_json), exist_ok=True)
    with open(output_json, 'w') as f:
        json.dump(output, f)

    file_size = os.path.getsize(output_json)
    with_doc = sum(1 for v in const_links.values() if v.get('docHtml'))
    print(f'  Extracted {len(module_docs)} module docstrings, '
          f'{len(const_links)} constants ({with_doc} with docstrings).')
    print(f'  Output: {file_size / 1024:.0f} KB')


if __name__ == '__main__':
    main()
