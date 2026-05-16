# `tao_review.tex` — documento integrador para Prof. T. Tao

Documento autocontenido (~30–50 páginas tras compilar) que presenta
el programa Andújar S189–S238 en su totalidad, con tono austero, alcance
honesto explícito, y todas las referencias a teoremas formales en Lean.

## Estructura

| Parte | Contenido |
|-------|-----------|
| **I**  | Framework — admissible inverse, translation identity, tensores binarios, S202 word, $\aS$. |
| **II** | Cylinder family $C_m$, función $\Cback(m, Q)$, grafo inverso, path-word correspondence. |
| **III**| BF closure, optimistic credit, S216 closure-to-barrier, status formal (8425+ jobs, 0 sorry). |
| **IV** | La única conjetura abierta (`S202_one_edge_count`), precise + coarse, conditional slope barrier. |
| **V**  | Markov/flow dual inspirado por Tao 2026, S230, S233, **el bug compartido detectado y corregido**, 3 ψ-certificates validados. |
| **VI** | S234 over-cover, dos preguntas concretas para AlphaEvolve, relación a Tao 2022. |

## Cómo compilar (recomendado: Overleaf)

1. Crea un proyecto nuevo en <https://overleaf.com>.
2. Sube **`tao_review.tex`** como archivo principal.
3. Compila con `pdfLaTeX` (motor por defecto).
4. Dos pasadas son suficientes (no hay BibTeX externo; las
   referencias están inline con `\begin{thebibliography}` en el
   documento, aunque este documento no las usa).

Tiempo de compilación esperado: ~10 segundos en Overleaf.

## Cómo compilar local (si tienes TeX Live / MikTeX)

```bash
cd paper/
pdflatex tao_review.tex
pdflatex tao_review.tex   # segunda pasada para TOC y referencias cruzadas
```

Dependencias: `amsmath`, `amsthm`, `amssymb`, `mathtools`,
`hyperref`, `booktabs`, `listings`, `xcolor`, `geometry`,
`microtype`, `babel`. Todas estándar.

## Antes de enviar a Tao

1. **Verifica la URL del repositorio** en el campo Reproducibility
   y en el cuadro de autor al final del documento.
2. **Verifica la fecha** (actualmente "May 2026") y el commit hash
   si quieres anclar a un commit específico (opcional pero
   recomendado para reviewers).
3. **Considera publicar primero en arXiv** y referenciar al ID
   antes del envío. Eso da número de identificación estable.

## Diferencia con `main.tex`

- `main.tex`: paper estándar de ~30 páginas para arXiv pública,
  centrado en S216 y la conjetura precise. Más conciso.
- `tao_review.tex`: documento de revisión exhaustivo, ~50 páginas,
  específicamente dirigido a Tao. Incluye **explícitamente** la
  historia del bug del miner S233 y los ψ-certificates corregidos.
  Es honestidad activa: muestra qué falló y cómo se corrigió.

Recomendación: enviar **ambos** a Tao en el mismo mensaje. `main.tex`
para visión general académica; `tao_review.tex` para revisión técnica
profunda.
