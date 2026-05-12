# AXLE — Axiom Lean Engine, ús en aquest projecte

Font: https://axle.axiommath.ai/v1/docs/

AXLE és un conjunt d'utilitats Lean 4 (metaprogrames sobre Lean + Mathlib) per
verificar candidats de prova, partir teoremes, convertir-los a `sorry`,
reparar proves, etc. És útil per al pipeline S189–S207 d'aquest repo perquè
permet auditar i transformar els fitxers `CollatzLean4/CollatzLean4/*.lean`
sense executar `lake build` complet.

## Instal·lació

```bash
pip install axiom-axle
```

Requereix Python ≥ 3.10. Compatible amb el toolchain Lean 4 que ja s'usa
a `CollatzLean4/lean-toolchain`.

Accés alternatiu:
- Web: https://axle.axiommath.ai/
- HTTP/REST API per integració directa.

## Comandes CLI principals

| Comanda                 | Ús                                                 |
|-------------------------|----------------------------------------------------|
| `axle verify-proof`     | Valida una prova candidata contra l'enunciat       |
| `axle check`            | Escaneja errors d'un fitxer/projecte Lean          |
| `axle extract-theorems` | Separa cada `theorem`/`lemma` en fitxers propis    |
| `axle extract-decls`    | Extreu definicions individuals                     |
| `axle repair-proofs`    | Intenta tancar `sorry` o proves trencades          |
| `axle simplify-theorems`| Simplifica proves verboses                         |
| `axle rename`           | Renombra símbols de forma consistent               |
| `axle theorem2lemma`    | Converteix `theorem` → `lemma`                     |
| `axle merge`            | Fusiona fitxers de proves                          |
| `axle normalize`        | Normalitza l'estil de les proves                   |

Manteniment: deployment públic actualitzat cada dimecres a les 10:00 PT
(downtime típic < 5 min).

## Workflow recomanat per al front admissible (S189–S207)

Mòduls nous afegits en aquesta sessió, tots a
`CollatzLean4/CollatzLean4/`:

- `AdmissibleBasic.lean` — `Branch`, `Word`, `tau`, `AdmState`, `step`,
  `evalWord`, identitat `3^q n + B = 2^A` (`evalWord_translation_identity`).
- `TranslationSets.lean` — `B_adm`, `B_free`, `R_adm`, `R_free`,
  `coverage_translation_equiv` (S191-E).
- `Defect.lean` — `defect`, dinàmica per branca, paraula `wS202`,
  contraexemple `not_forall_defect_nonnegative` (S202).
- `NegativeRuns.lean` — `LInt`, `Lnum`, criteri `n ≡ −1 (mod 3^k)` (S203-C).
- `PeriodicBlocks.lean` — dades S202 + punt fix 3-àdic mod `3^24` (S206)
  amb `native_decide`, i no-repetició directa des de 251.

Cicle típic amb AXLE:

```bash
# 1. Comprovació ràpida d'errors
axle check CollatzLean4/CollatzLean4/AdmissibleBasic.lean

# 2. Llistar sorries pendents
axle extract-theorems CollatzLean4/CollatzLean4/AdmissibleBasic.lean \
  --filter sorry

# 3. Intentar tancar sorries triviales (step_one_good, defect_step_*)
axle repair-proofs CollatzLean4/CollatzLean4/Defect.lean

# 4. Validar identitat central
axle verify-proof --name evalWord_translation_identity \
  CollatzLean4/CollatzLean4/AdmissibleBasic.lean

# 5. Normalitzar abans de commit
axle normalize CollatzLean4/CollatzLean4/*.lean
```

## Sorries oberts en aquesta entrega

Marcats amb `sorry` deliberadament — NO són axiomes:

- `AdmissibleBasic.step_one_good`, `step_zero_good`
  (preservació de la identitat de translació; el cas `zero` requereix
  divisibilitat `3 ∣ 2^τ(n) n − 1` per `n ∈ X`, prova per casos a `n % 9`).
- `NegativeRuns.negative_run_integrality_iff`
  (criteri `L^k(n) ∈ ℤ ⇔ n ≡ −1 (mod 3^k)`).
- `TranslationSets.coverage_translation_equiv` (S191-E).

Oberts NO formalitzats com a teoremes (resten conjectures):

- Accessibilitat des de 1 als cilindres del punt fix S202.
- Pendent asimptòtica `λ_asy < 2`.
- Cobertura completa `∀ n ∈ X, ∃ w, evalWord w .n = n`
  (equivalent al nucli Collatz dins aquest model).
- Distribució de `R_adm(A,q)`.

## Estat matemàtic

No es demostra Collatz. Es formalitza:
- la reformulació com a cobertura per translacions admissibles
  `3^q n + B = 2^A`;
- la falsedat de `A ≥ 2q` via S202 (`43/22 < 2`);
- l'existència d'un bloc de pendent baixa amb punt fix 3-àdic local
  (`a_w ≡ 31381059610 mod 3^24`, certificat per `native_decide`).
