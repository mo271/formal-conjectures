/**
 * theorem.js — powers the /theorem/ detail page.
 *
 * Renders the theorem detail view with:
 * - Module docstring (from Verso, with rendered LaTeX/HTML)
 * - Problem description (docstring from Verso, with rendered LaTeX)
 * - Syntax-highlighted Lean code (fetched on demand from the Verso literate page)
 * - Links to full annotated source and GitHub
 */

'use strict';

const detailEl = document.getElementById('theorem-detail');
const _base = document.documentElement.dataset.base || '';

async function init() {
  const params = new URLSearchParams(window.location.search);
  const name   = params.get('name');

  if (!name) {
    renderError(`No theorem name specified. Try browsing the <a href="${_base}/browse/">full list</a>.`);
    return;
  }

  let data;
  try {
    data = await FC.loadData();
  } catch (e) {
    renderError(`Could not load data: ${FC.escapeHTML(e.message)}`);
    return;
  }

  const theorem = data.conjectures.find(c => c.theorem === name);
  if (!theorem) {
    renderError(`Theorem <code>${FC.escapeHTML(name)}</code> not found. It may have been renamed or removed.`);
    return;
  }

  document.title = `${theorem.theorem} — Formal Conjectures`;
  const siblings = data.conjectures.filter(c => c.module === theorem.module);
  const verso = data.versoFragments || { moduleDocs: {}, constLinks: {} };

  renderDetail(theorem, siblings, verso);
}

/**
 * Find the Verso constant link for a theorem.
 * extract_names uses "FormalConjectures.ErdosProblems.830.erdos_830.parts.i"
 * Verso uses "Erdos830.erdos_830.parts.i".
 * We try progressively shorter suffixes.
 */
function findVersoLink(theoremName, constLinks) {
  const parts = theoremName.split('.');
  for (let i = 0; i < parts.length; i++) {
    const suffix = parts.slice(i).join('.');
    if (constLinks[suffix]) return constLinks[suffix];
  }
  return null;
}

/**
 * Load the Verso CSS for syntax highlighting and code block rendering.
 * Includes code.css and tippy-border.css from the deployed Verso pages,
 * plus critical inline rules to hide tactic states and warning messages.
 */
function loadVersoCss() {
  if (document.getElementById('verso-code-css')) return;

  // Load Verso's code.css for syntax highlighting
  const codeLink = document.createElement('link');
  codeLink.id = 'verso-code-css';
  codeLink.rel = 'stylesheet';
  codeLink.href = `${_base}/src/code.css`;
  document.head.appendChild(codeLink);

  // Load tippy border CSS for hover tooltips
  const tippyLink = document.createElement('link');
  tippyLink.rel = 'stylesheet';
  tippyLink.href = `${_base}/src/tippy-border.css`;
  document.head.appendChild(tippyLink);

  // Add critical inline CSS to properly hide Verso interactive elements
  // that are normally hidden on the Verso source pages
  const style = document.createElement('style');
  style.textContent = `
    /* Hide tactic goal states (shown via checkbox toggle on Verso pages) */
    .hl.lean .tactic-state { display: none; }
    .hl.lean .tactic-toggle { position: absolute; opacity: 0; height: 0; width: 0; }
    .hl.lean .tactic-toggle:checked ~ .tactic-state { display: inline-block; }
    /* Hide compiler messages (shown via hover on Verso pages) */
    .hover-info.messages { display: none; }
    /* Style warning underlines */
    .hl.lean .has-info .token:not(.tactic-state) {
      text-decoration-style: wavy;
      text-decoration-line: underline;
    }
    .hl.lean .has-info.warning .token:not(.tactic-state) {
      text-decoration-color: #c09020;
    }
    /* Style inter-text spacing */
    .hl.lean .inter-text { white-space: pre; }
  `;
  document.head.appendChild(style);
}

/**
 * Fetch the highlighted code block for a theorem from its Verso page.
 * Returns the HTML string of the <code class="hl lean block"> element
 * containing the theorem definition.
 */
async function fetchVersoCodeBlock(versoLink) {
  try {
    const pageUrl = `${_base}/src${versoLink.url.split('#')[0]}`;
    const resp = await fetch(pageUrl);
    if (!resp.ok) return null;
    const html = await resp.text();

    // Parse the HTML and find the code block containing our theorem's anchor
    const parser = new DOMParser();
    const doc = parser.parseFromString(html, 'text/html');
    const anchor = doc.getElementById(versoLink.anchor);
    if (!anchor) return null;

    // Walk up to find the enclosing <code class="hl lean block">
    let el = anchor;
    while (el && !(el.tagName === 'CODE' && el.classList.contains('hl'))) {
      el = el.parentElement;
    }
    if (!el) return null;

    // Also grab the hover data script for this page
    const hoverScript = doc.querySelector('script[type="verso-hovers"]');
    const hoverData = hoverScript ? hoverScript.textContent : null;

    return { codeHtml: el.outerHTML, hoverData };
  } catch (e) {
    console.warn('Failed to fetch Verso code:', e);
    return null;
  }
}

function renderError(msg) {
  detailEl.innerHTML = `
    <div class="theorem-detail__breadcrumb">
      <a href="${_base}/browse/">&larr; Browse</a>
    </div>
    <div class="empty-state">
      <div class="empty-state__text">${msg}</div>
    </div>`;
}

function renderDetail(theorem, siblings, verso) {
  const catMeta = FC.getCategoryMeta(theorem.category);

  // Subject pills
  const subjectPillsHTML = theorem.subjects.length
    ? theorem.subjects.map(s =>
        `<span class="subject-pill">${FC.escapeHTML(s.name)} <span style="opacity:.6;font-size:.75em">(${FC.escapeHTML(s.code)})</span></span>`
      ).join('\n')
    : '<span style="color:var(--color-text-muted);font-size:.875rem">None listed</span>';

  // Collection link
  const collectionHTML = theorem.collectionUrl
    ? `<a href="${FC.escapeHTML(theorem.collectionUrl)}" target="_blank" rel="noopener">${FC.escapeHTML(theorem.collection)}</a>`
    : FC.escapeHTML(theorem.collection);

  // Siblings
  const siblingsHTML = siblings.length > 1
    ? siblings.map(s => {
        const isCurrent = s.theorem === theorem.theorem;
        const sCatMeta = FC.getCategoryMeta(s.category);
        return `
          <div class="sibling-item ${isCurrent ? 'current' : ''}">
            <span class="badge ${sCatMeta.css}">${FC.escapeHTML(sCatMeta.label)}</span>
            ${isCurrent
          ? `<span style="font-weight:500;color:var(--color-text)">${FC.escapeHTML(s.theorem)}</span>`
          : `<a href="${FC.escapeHTML(FC.theoremURL(s.theorem))}">${FC.escapeHTML(s.theorem)}</a>`}
          </div>`;
      }).join('\n')
    : '';

  // --- Verso data ---
  // sourceUrl is like "/src/FormalConjectures/..." but verso keys don't have /src prefix
  const moduleDocKey = (theorem.sourceUrl || '').replace(/^\/src/, '');
  const moduleDocHTML = verso.moduleDocs[moduleDocKey] || '';
  const versoLink = findVersoLink(theorem.theorem, verso.constLinks);
  const docHtml = versoLink && versoLink.docHtml ? versoLink.docHtml : '';

  // versoLink.url is already like "/FormalConjectures/.../#anchor"
  const versoSourceUrl = versoLink
    ? `${_base}/src${versoLink.url}`
    : theorem.sourceUrl
      ? `${_base}${theorem.sourceUrl}`
      : null;

  // Module overview section (from Verso)
  const moduleDocSection = moduleDocHTML ? `
    <div class="theorem-detail__section verso-module-doc">
      <div class="detail-label">Module overview</div>
      <div class="verso-doc-content">${moduleDocHTML}</div>
    </div>` : '';

  // Problem description (from Verso docstring, with HTML/LaTeX)
  const docSection = docHtml ? `
    <div class="theorem-detail__section">
      <div class="detail-label">Problem description</div>
      <div class="verso-doc-content">${docHtml}</div>
    </div>` : '';

  // Code placeholder (will be filled by async fetch)
  const codeSection = versoLink ? `
    <div class="theorem-detail__section">
      <div class="detail-label">
        Lean code
        ${versoSourceUrl ? `<a href="${versoSourceUrl}" target="_blank" rel="noopener"
           style="font-weight:400;font-size:.8rem;margin-left:.5rem">view full source ↗</a>` : ''}
      </div>
      <div id="verso-code-container" class="verso-code-container">
        <div class="verso-code-loading">Loading highlighted code…</div>
      </div>
    </div>` : '';

  detailEl.innerHTML = `
    <div class="theorem-detail__breadcrumb">
      <a href="${_base}/browse/">&larr; Browse</a>
      &nbsp;&rsaquo;&nbsp;
      <a href="${_base}/browse/?collection=${encodeURIComponent(theorem.collection)}">${FC.escapeHTML(theorem.collection)}</a>
    </div>

    <header class="theorem-detail__header">
      <h1 class="theorem-detail__title">${FC.escapeHTML(theorem.theorem)}</h1>
      <span class="badge ${catMeta.css}" style="font-size:.9rem;padding:.3rem .9rem">${FC.escapeHTML(catMeta.label)}</span>
    </header>

    ${moduleDocSection}

    ${docSection}

    ${codeSection}

    <div class="theorem-detail__section">
      <div class="detail-label">Module</div>
      <div class="detail-mono">${FC.escapeHTML(theorem.module)}</div>
    </div>

    <div class="theorem-detail__section">
      <div class="detail-label">Source collection</div>
      <div class="detail-value">${collectionHTML}</div>
    </div>

    <div class="theorem-detail__section">
      <div class="detail-label">AMS subjects</div>
      <div style="display:flex;flex-wrap:wrap;gap:.4rem;margin-top:.25rem">
        ${subjectPillsHTML}
      </div>
    </div>

    ${siblings.length > 1 ? `
    <div class="theorem-detail__section">
      <div class="detail-label">Other results in this file</div>
      <div class="siblings-list">
        ${siblingsHTML}
      </div>
    </div>` : ''}

    <nav class="theorem-detail__nav" aria-label="Page actions">
      <a href="${_base}/browse/" class="btn btn-outline">&larr; Back to browse</a>
      ${versoSourceUrl ? `<a href="${versoSourceUrl}" class="btn btn-outline">View annotated source</a>` : ''}
      <a href="${FC.escapeHTML(theorem.githubUrl)}" class="btn btn-outline" target="_blank" rel="noopener">
        View on GitHub ↗
      </a>
    </nav>
  `;

  // Render LaTeX in docstrings using KaTeX auto-render
  renderLatex();

  // Async: fetch and render the highlighted code block
  if (versoLink) {
    loadVersoCss();
    fetchVersoCodeBlock(versoLink).then(result => {
      const container = document.getElementById('verso-code-container');
      if (!container) return;
      if (result && result.codeHtml) {
        container.innerHTML = result.codeHtml;
      } else {
        container.innerHTML = `<div class="verso-code-fallback">
          <a href="${versoSourceUrl || '#'}">View in annotated source →</a>
        </div>`;
      }
    });
  }
}

/**
 * Render LaTeX in docstring elements using KaTeX auto-render.
 * Waits for KaTeX to be loaded (it's deferred), then processes
 * all .verso-doc-content elements.
 */
function renderLatex() {
  // KaTeX auto-render is loaded with defer, so it may not be ready yet
  function doRender() {
    if (typeof renderMathInElement !== 'function') {
      // KaTeX not loaded yet, retry
      setTimeout(doRender, 100);
      return;
    }
    for (const el of document.querySelectorAll('.verso-doc-content')) {
      renderMathInElement(el, {
        delimiters: [
          { left: '$$', right: '$$', display: true },
          { left: '\\\\[', right: '\\\\]', display: true },
          { left: '$', right: '$', display: false },
          { left: '\\\\(', right: '\\\\)', display: false },
        ],
        throwOnError: false,
      });
    }
  }
  doRender();
}

init();
