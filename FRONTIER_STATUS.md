# Estado de fronteras — programa S189–S242

**Fecha:** 2026-06-01 (consolidación S240–S242; sustituye íntegramente la versión 2026-05-14)
**Resumen:** el arco S240–S242 cerró la frontera computacional por **forma cerrada**
(ya no hay tabla de certificados que escalar), cartografió con teoremas la muerte de la
κ-ruta, completó el pipeline de ciclos de Hercher, y aisló la dificultad del problema
con nombre propio. 26 commits verificados, 0 `sorry`; 9 anclas `native_decide`
**eliminadas** del corpus (AS202Lift des-anclado).

## 1. Barrera de divergencia (Wall-B): estado final del arco

### Resuelto en FORMA CERRADA (sin búsqueda, sin tablas, sin native_decide)

| Enunciado | Teorema | Axiomas |
|---|---|---|
| Barrera κ acotada, criterio de bits `4(m+Q)+1 ≤ size(start)` | `kappa_bounded_barrier_bitlen` (BitlenPotential) | limpio |
| Start genérico (zócalo para cualquier representante) | `kappa_bounded_barrier_bitlen_from` | limpio, sin anclas |
| Uniforme `m+Q ≤ 8` (start Caveat-C) | `kappa_barrier_of_sum_le_eight` | + ancla aS202 |
| m=1 hasta Q=7 | `kappa_barrier_m1_Q7` | + ancla aS202 |
| **FIEL m=2 hasta Q=16** (antes "⛔ bloqueado") | `kappa_barrier_at_m2_Q16` (FaithfulBarrier) | **limpio, sin anclas** |
| **FIEL m=3 hasta Q=23** | `kappa_barrier_at_m3_Q23` | **limpio, sin anclas** |

El criterio de bits es exactamente justo (73=73, 105=105). La tabla de fronteras
computacionales de la versión anterior queda **obsoleta**: la forma cerrada cubre y
excede todo lo que el motor BF había certificado (m=1: Q≤7 ⊃ Q≤5; m=2: Q≤16 ⊃ Q≤9;
m=3: Q≤23 ⊃ Q≤6) sin coste computacional.

### El mapa de obstrucciones (todo machine-checked)

* La κ-inducción por bloques es **CIRCULAR** (`KappaPathSplit ⟺ barrier(m+1)`, IVT discreto).
* El dispositivo canonical-first-split es **FALSO** (`not_firstMPrecisionSuffixPositive`,
  `not_blockBoundaryExists` — la escalera de ~10²¹ aristas existe por argumento cerrado).
* **No hay invariante de congruencia** a ningún módulo: `invReachable_units` (ReachUnits)
  — todo cilindro unidad es alcanzable a toda precisión (pieza C cerrada en positivo).
* **Ningún potencial 3-ádicamente continuo** certifica la barrera, en NINGÚN codominio:
  colapso ℤ (S241) + `no_decaying_modulus_corrector` (AttractorNoGo, vía los atractores
  ±1 y `ν₃(aS202−1) = 22`): todo módulo de continuidad ω cumple `m ≤ ω(22+Q)`.
* Clase tropical/Green **refutada** con testigo (gate de cociente); reducción Sturmiana
  **muerta** (los caminos óptimos son el filamento τ=1, `min-κ(j) = −j`).
* Muro real del potencial de bits: `Q ~ 22m` (toda Φ lineal en (bitlen, j) muere ahí).

### Lo que queda abierto (con nombre)

1. **Rincón híbrido**: parte singular Green + resto Hölder (acotado `L ≥ 2·3^{5α}`,
   vivo; el gate `phi_realkam_lp.py` se extiende reponderando aristas).
2. **CMS ("Mason–Stothers de acarreos")**: cualquier δ′>0 efectivo en el conteo de
   acarreos por palabra admisible extiende PhiBitlen más allá de Q~22m. Único
   incondicional conocido: Stewart 1980 (log log — la pared Baker disfrazada).
3. Migración Caveat-C a nivel de PALABRAS (`S216BarrierForWords` con `aS202_at`).

## 2. Mitad de ciclos (Wall-A): pipeline Hercher completo

| Resultado | Estado |
|---|---|
| m = 1, 2, 3, 4 sin ciclos no triviales | **INCONDICIONAL** (CycleEquation, Baker-free) |
| Ventana bilateral `m·log₂3 < A < 2m` | **INCONDICIONAL** (corredor maestro + 1b) |
| Corredor maestro `3^q·a₀ < 2^A·Syr^[q]a₀ ≤ 4^q·a₀` | **INCONDICIONAL**, sin hipótesis de ciclo |
| Sin ciclo de período < 359 | condicional a `SyrVerifiedUpTo 2²⁰` (≈10⁶) |
| Sin ciclo de período < 16 266 | condicional a `SyrVerifiedUpTo 2²⁹` (≈5·10⁸) |
| Puente literatura: `CollatzVerifiedUpTo (3X+1) → SyrVerifiedUpTo X` | probado (CollatzBridge) |
| Techo general | **ABIERTO** (ni Baker efectivo lo cierra; ratchet = ecuación + cómputo + convergentes) |

`fastPowAux` (potencia binaria con fuel) desbloquea pares de convergentes arbitrarios:
el techo de M₀ lo pone el tiempo de multiplicación GMP del kernel, no la recursión.

## 3. La dificultad, nombrada (S241–S242)

Las cuatro paredes residuales son **un solo objeto**: la aproximación racional efectiva
de log₂3 — equivalentemente, **el proceso sturmiano de acarreos de la plaza arquimediana
de ℚ** (`size(3n+1) − size(n) ∈ {1,2}` con número de rotación log₂3). El gemelo sobre
𝔽₂[x] (Hicks–Mullen–Yucas–Zavislak 2008 + Behajaina–Paran 2023/25 + conjugación de
Monks 2025) es **teorema** precisamente porque allí no hay acarreos (deg es exacto) —
y el "Baker funcional" ingenuo es FALSO allí (gaps unidad infinitos por Frobenius) sin
impedir el teorema: la dificultad entera NO es solo "falta Baker efectivo".

## 4. Próximo arco

1. ~~**Formalización 𝔽₂[x]**~~ ✅ **HECHA** (S243, `F2Collatz.lean`): el teorema HMYZ
   completo `collatz_F2X : ∀ f ≠ 0, ∃ k, T^[k] f = 1`, primera formalización conocida.
   Las leyes de grado EXACTAS (gemelas de `size_two_pow_mul`/`size_three_mul_add_one`),
   la no-divergencia puntual `deg(T^[k]f) ≤ deg f + 1`, y la salida de meseta por el
   **telescopio de meseta** `x·(T²f+1) = (x+1)·(f+1)` (más fino que el argumento de
   orden multiplicativo de la literatura: cada paso de meseta consume exactamente un
   factor `x` de `f+1` — álgebra de anillos pura, sin Frobenius). Axiomas:
   {propext, Classical.choice, Quot.sound}. El experimento de control queda
   teorema-vs-teorema dentro del propio repo.
2. Paper 1 (obstrucciones machine-checked) — outline en `PAPER1_OUTLINE.md`.
3. Gate híbrido (1 run de agente) — brasa lenta.
4. Bonus 𝔽₂[x] (opcional): `gap_isUnit_iff` — la clasificación Frobenius–Catalan
   `x^A + (x+1)^m = 1 ⟺ A = m = 2^k` (candidata a PR de Mathlib).
