# tools/ — toolchain Python ↔ Lean para certificados S202/S216

Cadena externa que **produce los datos** (tablas BF cerradas sobre el
grafo inverso de cilindros) que el lado Lean (`CollatzLean4/`)
**verifica formalmente** vía `native_decide`. El teorema
`S216_barrier_for_words_outgoing` ya cierra el paso
**certificado → barrera terminal** sin huecos: cada certificado
listado abajo produce un teorema `S216BarrierForWords m Q T`.

## Estructura

```
tools/
├── s202_engine.py            # motor original (DFS con corte d < T)
├── s216_engine.py            # motor BF con crédito optimista d − (Q−j) < T  ← canónico
├── cert_to_lean.py           # exporter v1 (S202 closure, deprecado)
├── cert_to_lean_s216.py      # exporter v2 (S216 BF + chunked tables)   ← canónico
├── emit_barrier_adapter.py   # genera el adaptador Bool→Prop por (m,Q)
├── s216_colab.py             # script monolítico para Colab/TPU (legacy, contenía bug)
├── s216_colab_debug.py       # script Colab corregido con sanity automática  ← canónico
├── s216_engine.py            # (ver arriba)
└── s216_frontier_results.json  # resultados crudos de la última corrida
```

## Modelo de cálculo: arista, peso, cierre

El grafo `(j, c)` y sus aristas inversas vienen de
[CollatzLean4/InverseGraph.lean](../CollatzLean4/CollatzLean4/InverseGraph.lean).
El peso de cada arista **es la contribución al defecto**
`D(u) = A(u) − 2·q(u)`:

| Tipo | Cambio de `j` | Peso |
|------|---------------|------|
| One-edge (τ = t ∈ {1,2,3,4})  | igual    | `t`     |
| Zero-edge (τ = t ∈ {1,2,3,4}) | `+1`     | `t − 2` |

Regla de cierre **optimista** S216 (única correcta — la naïve `d < T`
descarta caminos que un zero-edge τ=1 todavía puede empujar bajo `T`):

```
(s, d) es relevante  ⇔  d − (Q − j(s)) < T
```

con `T = m` por defecto. La barrera dice: *si ningún goal* `c = 1`
es alcanzable con `d < T` desde `start = (0, aS202_at(m) mod 3^R)`,
entonces `𝒞^←_{S202}(m, Q) ≥ T`.

## Uso

```bash
# 0. Sanity check del motor (debe imprimir n=251, A=43, q=22 para W202)
python tools/s202_engine.py

# 1. Generar certificado Lean + adaptador para (m, Q)
python tools/cert_to_lean_s216.py 1 10 \
    > CollatzLean4/CollatzLean4/Cert_m1_Q10_S216.lean
# (el _Barrier.lean por ahora se clona a mano del de Q=8; la
#  plantilla se reemite con emit_barrier_adapter.py — ver §Ejecución
#  reproducible)

# 2. Añadir el import al root:
#    CollatzLean4/CollatzLean4.lean:
#       import CollatzLean4.Cert_m1_Q10_S216_Barrier

# 3. Compilar
cd CollatzLean4 && lake build CollatzLean4.Cert_m1_Q10_S216_Barrier

# 4. Verificación rápida en Colab / TPU (sólo si la tabla supera lo
#    que el portátil puede mover en minutos)
python tools/s216_colab_debug.py
```

`s216_colab_debug.py` ejecuta **primero el sanity** contra valores
canónicos `(m=1,Q=3)→35`, `(m=1,Q=5)→462`, `(m=1,Q=8)→24310`,
`(m=2,Q=6)→3003` y **sólo si pasa** corre el frontier. Esto evita
silenciosos veredictos "✓ holds" vacuos cuando el grafo no se
explora correctamente.

## Estado: qué está cerrado en Lean (al 2026-05-14)

| `m` | `Q` | `R` | estados BF | tiempo CPU | módulo Lean | barrera formal |
|----:|----:|----:|-----------:|-----------:|-------------|----------------|
| 1   | 3   | 24  |         35 |   <0.01 s  | `Cert_m1_Q3_S216_Barrier`  | ✅ `S216BarrierForWords 1 3 1` |
| 1   | 5   | 24  |        462 |    0.01 s  | `Cert_m1_Q5_S216_Barrier`  | ✅ `S216BarrierForWords 1 5 1` |
| 1   | 8   | 24  |     24 310 |    0.14 s  | `Cert_m1_Q8_S216_Barrier`  | ✅ `S216BarrierForWords 1 8 1` |
| 1   | 10  | 24  |    352 716 |    2.18 s  | `Cert_m1_Q10_S216_Barrier` | 🟡 emitido — build pendiente |

## Estado: fronteras computacionalmente cerradas, **lift Lean bloqueado**

Las siguientes barreras están **computacionalmente cerradas** por
`s216_engine.py` (BF con cierre optimista, sin goals alcanzables) pero
**no se pueden levantar a Lean** todavía porque `InvStart` usa
`aS202 mod 3^(22m+2)` — un representante incorrecto para `m ≥ 2`,
ver [CollatzLean4/AS202Lift.lean:106-130](../CollatzLean4/CollatzLean4/AS202Lift.lean#L106-L130):

| `m` | `Q` | `R` | estados BF | tiempo CPU | bloqueo |
|----:|----:|----:|-----------:|-----------:|---------|
| 2   | 9   | 46  |    167 960 |    1.01 s  | refactor `InvStart` → `aS202_at` |
| 3   | 6   | 68  |      5 005 |    0.02 s  | refactor `InvStart` → `aS202_at` |

El refactor son **4 pasos** descritos en `AS202Lift.lean:108-128`:
1. Generalizar `InvStart` para usar `aS202_at m`.
2. Generalizar el cilindro en `S216BarrierForWords`.
3. Reprobar `deltaPlus_aS202_general` (la cota `R − 22` se conserva
   porque `ν₃(aS202_at m − 1) = 22` para todo `m`).
4. Cambiar `cert_to_lean_s216.py` para emitir contra `aS202_at m`.

## Significado matemático

Una barrera `S216BarrierForWords m Q T` formaliza:

> ∀ palabra admisible `u` con `q(u) ≤ Q` y `n(u) ≡ aS202_at m (mod 3^R)`,
> `D(u) ≥ T`.

Combinada con `S202_one_edge_count_conjecture` (el único hueco abierto
del programa, ver [HANDOFF_COLLATZ_ROADMAP.md](../HANDOFF_COLLATZ_ROADMAP.md)),
esto cierra la rama analítica del programa S189–S220 hacia Collatz.

## Notas reproducibles

* `s216_engine.py` es la única fuente de verdad. El sanity de referencia
  vive en su `__main__`.
* El bug histórico del Colab v1 era usar pesos `1` / `{−1, 0}` en lugar de
  `τ` / `τ−2`. Detectable por `goals_seen=0` y `expanded=max_states`
  silenciosamente — siempre confirmar contra el sanity.
* Los certificados `Q ≥ 10` superan 800 filas y se emiten **en
  chunks** de ≤500; ver `CHUNK_THRESHOLD` en `cert_to_lean_s216.py`.
* `set_option maxHeartbeats 0` y `maxRecDepth 500000` son obligatorios
  para que `native_decide` cierre tablas grandes.
