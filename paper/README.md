# paper/ — manuscritos del programa S189–S220

## Estructura

| Archivo | Rol | Estado |
|---------|-----|--------|
| [main.tex](main.tex) | **Manuscrito principal arXiv** — overview integrador del programa con tono austero, abstract autocontenido, una sola conjetura abierta explícita, apéndice de reproducibilidad. | listo para arXiv |
| [s216_paper.tex](s216_paper.tex) | Companion técnico de S216 (BF closure → barrera terminal), versión doble-ciego pensada para evaluación de artefactos. | listo para arXiv como companion |
| [s214_core_section.tex](s214_core_section.tex) | Sección S214 (potenciales 3-ádicos locales) incluida como `\input` en `s216_paper.tex`. | sección, no standalone |
| [s214_core.tex](s214_core.tex) | Wrapper standalone para `s214_core_section.tex`. | listo |
| [abstract.txt](abstract.txt) | Abstract en texto plano para el formulario arXiv. | listo |


## Compilación

```bash
cd paper/
pdflatex main.tex
pdflatex main.tex     # segunda pasada para ToC y referencias cruzadas
```

Compila bajo TeX Live 2024 o MikTeX con los paquetes estándar
(`amsmath`, `amsthm`, `amssymb`, `mathtools`, `hyperref`, `booktabs`,
`listings`, `xcolor`, `geometry`, `microtype`, `babel`). No depende
de bibliografía externa (`\begin{thebibliography}` inline).

Para compilación online, copiar `main.tex` a un proyecto fresco de
Overleaf (motor LaTeX por defecto).

## Orden recomendado de envío

1. **`main.tex`** primero, a `math.NT` con cross-list a `math.DS` y
   `cs.LO`. Espera el ID arXiv.
2. **Repositorio en Zenodo** para obtener DOI archival. Actualiza
   `\appendix` de `main.tex` con URL del repo y commit hash.
3. **`s216_paper.tex`** como companion preprint que referencia al
   principal.

## Versionado

- v1: envío inicial.
- v2 (esperado en ~días): tras endorsement / feedback inicial, con
  URL/commit insertados y cualquier corrección menor de prueba.
- v3+: tras cerrar la tercera frontera (`Cert_m2_Q9` y `Cert_m3_Q6`
  formales en Lean) o tras avances en
  `S202_one_edge_count_conjecture`.

## Doble-ciego vs autoría completa

- `main.tex`: **NO doble-ciego** (autor declarado). Es la versión
  arXiv-ready para divulgación pública del programa.
- `s216_paper.tex`: **doble-ciego** (`\author{}` vacío). Pensado para
  conference de verificación formal (CPP, ITP, CADE) con revisión
  doble-ciego. Si el destino final es revista standard, eliminar la
  línea `\author{}` y añadir bloque de autor.

## Material suplementario (ancillary files)

- `tools/s216_engine.py` — implementación de referencia.
- `tools/s216_colab_debug.py` — script Colab con sanity check.
- `tools/cert_to_lean_s216.py` — exporter a Lean.
- `tools/s216_frontier_results.json` — resultados crudos.
- `CollatzLean4/` — desarrollo Lean completo (preferible alojar en
  GitHub + Zenodo y referenciar por DOI).

## Reproducibilidad

Verificación de un solo comando:

```bash
git clone <repo URL>
cd collatz-admissible-tree/CollatzLean4
lake exe cache get        # descarga Mathlib precompilado
lake build                # ~5–20 min en hardware estándar
```

Independiente del Lean, sanity Python:

```bash
python tools/s216_engine.py
python tools/s216_colab_debug.py   # phase-1 sanity + phase-2 frontier
```
