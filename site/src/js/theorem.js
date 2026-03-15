/**
 * theorem.js — powers the /theorem/ detail page.
 *
 * Reads ?name= from the URL, finds the theorem in the loaded data,
 * and renders the full detail view with module docstring, code, and links.
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

  // Update page title
  document.title = `${theorem.theorem} — Formal Conjectures`;

  // Find siblings (same module)
  const siblings = data.conjectures.filter(c => c.module === theorem.module);

  // Get Verso fragments
  const verso = data.versoFragments || { moduleDocs: {}, constLinks: {} };

  renderDetail(theorem, siblings, verso);
}

/**
 * Find the Verso constant link for a theorem.
 * extract_names uses fully-qualified names like "FormalConjectures.ErdosProblems.830.erdos_830.parts.i"
 * but Verso uses Lean namespace names like "Erdos830.erdos_830.parts.i".
 * We try progressively shorter suffixes of the theorem name.
 */
function findVersoLink(theoremName, constLinks) {
  // Try the full name first (after stripping module prefix)
  const parts = theoremName.split('.');
  for (let i = 0; i < parts.length; i++) {
    const suffix = parts.slice(i).join('.');
    if (constLinks[suffix]) return constLinks[suffix];
  }
  return null;
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

  // Subject pills HTML
  const subjectPillsHTML = theorem.subjects.length
    ? theorem.subjects.map(s =>
        `<span class="subject-pill">${FC.escapeHTML(s.name)} <span style="opacity:.6;font-size:.75em">(${FC.escapeHTML(s.code)})</span></span>`
      ).join('\n')
    : '<span style="color:var(--color-text-muted);font-size:.875rem">None listed</span>';

  // Collection link
  const collectionHTML = theorem.collectionUrl
    ? `<a href="${FC.escapeHTML(theorem.collectionUrl)}" target="_blank" rel="noopener">${FC.escapeHTML(theorem.collection)}</a>`
    : FC.escapeHTML(theorem.collection);

  // Siblings list
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
  // Module docstring: use sourceUrl as key (e.g. "/FormalConjectures/ErdosProblems/«830»/")
  // sourceUrl already has the right format with guillemets
  const moduleDocKey = theorem.sourceUrl || '';
  const moduleDocHTML = verso.moduleDocs[moduleDocKey] || '';

  // Find Verso const link for this theorem
  const versoLink = findVersoLink(theorem.theorem, verso.constLinks);
  const versoIframeUrl = versoLink
    ? `${_base}/src${versoLink.url}`
    : theorem.sourceUrl
      ? `${_base}/src${theorem.sourceUrl}`
      : null;

  // Module docstring section
  const moduleDocSection = moduleDocHTML ? `
    <div class="theorem-detail__section verso-module-doc">
      <div class="detail-label">Module overview</div>
      <div class="verso-doc-content">${moduleDocHTML}</div>
    </div>` : '';

  // Docstring section (from extract_names)
  const docstringSection = theorem.docstring ? `
    <div class="theorem-detail__section">
      <div class="detail-label">Problem description</div>
      <div class="verso-doc-content docstring-content">${FC.escapeHTML(theorem.docstring)}</div>
    </div>` : '';

  // Lean statement section (from extract_names)
  const statementSection = theorem.statement ? `
    <div class="theorem-detail__section">
      <div class="detail-label">Lean statement</div>
      <pre class="lean-statement"><code>${FC.escapeHTML(theorem.statement)}</code></pre>
    </div>` : '';

  // Annotated source iframe section
  const iframeSection = versoIframeUrl ? `
    <div class="theorem-detail__section">
      <div class="detail-label">
        Annotated source
        <a href="${versoIframeUrl}" target="_blank" rel="noopener"
           style="font-weight:400;font-size:.8rem;margin-left:.5rem">↗ open full page</a>
      </div>
      <div class="verso-iframe-container">
        <iframe src="${versoIframeUrl}"
                class="verso-iframe"
                title="Annotated Lean source"
                loading="lazy"
                sandbox="allow-scripts allow-same-origin"></iframe>
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

    ${docstringSection}

    ${statementSection}

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

    <div class="theorem-detail__section">
      <div class="detail-label">View source</div>
      <div class="detail-value" style="display:flex;flex-direction:column;gap:.4rem">
        <a href="${_base}${FC.escapeHTML(theorem.sourceUrl)}">
          Annotated source (with hovers &amp; docstrings)
        </a>
        <a href="${FC.escapeHTML(theorem.githubUrl)}" target="_blank" rel="noopener">
          ${FC.escapeHTML(theorem.module.replace(/\./g, '/'))}.lean on GitHub ↗
        </a>
      </div>
    </div>

    ${siblings.length > 1 ? `
    <div class="theorem-detail__section">
      <div class="detail-label">Other results in this file</div>
      <div class="siblings-list">
        ${siblingsHTML}
      </div>
    </div>` : ''}

    ${iframeSection}

    <nav class="theorem-detail__nav" aria-label="Page actions">
      <a href="${_base}/browse/" class="btn btn-outline">&larr; Back to browse</a>
      <a href="${_base}${FC.escapeHTML(theorem.sourceUrl)}" class="btn btn-outline">
        View annotated source
      </a>
      <a href="${FC.escapeHTML(theorem.githubUrl)}" class="btn btn-outline" target="_blank" rel="noopener">
        View on GitHub ↗
      </a>
    </nav>
  `;
}

init();
