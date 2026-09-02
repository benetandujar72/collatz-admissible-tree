# arXiv submission sheet — Paper 1 (v1, June 2026)

Everything below is ready to paste into https://arxiv.org/submit.
The only steps Claude cannot do for you are logging in and pressing Submit.

## 0. Pre-flight (done)

- Source compiles standalone (tectonic 0.16.9 locally; standard pdflatex
  toolchain on arXiv — amsart, no figures, no shell-escape, bibliography
  inline). 18 pages, 0 errors, 0 undefined references.
- Every Lean name cited in the text verified to exist in the repository
  (`check_paper.py`), and audited per declaration (`AxiomAudit.lean`).
- Bibliography verified against the live records (Hercher JIS 26 23.3.5;
  HMYZ AMM 115(7); Behajaina–Paran FFA 91 (2023) 102265 + arXiv:2312.00390;
  Alon–Behajaina–Paran arXiv:2401.03210).
- Repo tag for the artifact snapshot: `arxiv-v1`.

## 1. What to upload

Upload **only** `paper1/main.tex` (or the zip `paper1-arxiv-v1.zip`, same
content). No ancillary files needed — the Lean artifact is linked by URL.

## 2. Metadata (copy–paste)

**Title**

```
Machine-checked obstructions for potential-based approaches to the Collatz conjecture, with closed-form bounded barriers
```

**Authors**

```
Benet Andújar Guardado
```

**Abstract** (TeX math allowed in this field; under the 1920-char limit)

```
We formalize, in Lean 4 over a single verified graph model -- the admissible
inverse cylinder tree of the accelerated Syracuse map -- an obstruction map
for four natural families of "local potential" proof strategies aimed at the
divergence half of the Collatz problem, together with the strongest
closed-form positive results those obstructions permit. The negative results
are theorems, not heuristics: the per-block induction route is closed (its
naive count form is provably equivalent to the barrier it was meant to
prove, and the crux of its non-circular form is refuted by an explicit
astronomical one-edge ladder); no congruence invariant separates start from
goal at any finite modulus (every unit cylinder is reachable); no potential
with a $Q$-independent 3-adic continuity modulus certifies the barrier
uniformly in $Q$, in any codomain; and the linear bit-length class, which
certifies the barrier in closed form exactly up to a bit criterion, dies at
the very next step -- and enriching it with singular poles at the two
attractors does not move the wall by a single step (an LP-duality argument
whose rational Farkas certificates are themselves checked in Lean). The
positive results include the closed-form bit-length potential, and a
kernel-checked formalization of Eliahou's continued-fraction cycle
reduction. The residual difficulty is isolated as a single named phenomenon
-- the archimedean Sturmian carry process of rotation number $\log_2 3$ --
for which the function-field analogue over $\mathbb{F}_2[x]$, here
formalized end-to-end, serves as a control experiment. Every declaration
cited depends only on the three standard Lean axioms (machine-audited). The
Collatz conjecture itself remains, of course, wide open; the contribution is
a machine-checked map of where its difficulty does and does not live.
```

**Primary classification**: `math.NT` (Number Theory)

**Cross-list**: `math.LO` (Logic) — alternatively or additionally `cs.LO`
(Logic in Computer Science), where most Lean/Mathlib formalization papers
also live. Recommended: cross-list both `math.LO` and `cs.LO`.

**MSC classes**

```
11B83 (Primary), 68V20, 11Y50, 03B35 (Secondary)
```

**Comments field**

```
18 pages. Lean 4 artifact (zero sorry; machine-generated per-declaration axiom audit):
https://github.com/benetandujar72/collatz-admissible-tree, tag arxiv-v1
```

**License**: the default arXiv non-exclusive license is fine and keeps all
options open for journal submission later. Choose CC BY 4.0 instead only if
you want maximal reuse from day one (harder to undo). Recommendation:
**arXiv non-exclusive** for v1.

## 3. Submission steps (manual, ~10 minutes)

1. Log in at arxiv.org (account: bandujar@edutac.es — matches the paper's
   contact email).
2. *Endorsement*: a first submission to math.NT REQUIRES an endorsement by
   an established author of that archive (arXiv policy since January 2026).
   The form gives you an endorsement code and link; send it privately to a
   colleague who has published in math.NT (the Zulip #maths community and
   the authors you cite are natural candidates). Budget one to several days.
3. Start New Submission → license → upload `main.tex` → let AutoTeX process
   (it will produce the PDF; check the log shows no errors) → preview the
   PDF.
4. Paste the metadata above. Submit.
5. Announcement: submissions complete before 14:00 ET on a weekday are
   announced the next business day at ~20:00 ET. The arXiv ID
   (YYMM.NNNNN, e.g. 2609.NNNNN) is assigned when the paper is announced.

## 4. After the ID arrives

- Add the arXiv badge/ID + link to the repository README.
- `git tag arxiv-YYMM.NNNNN && git push --tags` (optional convenience tag).
- The paper's §9 invites re-checking; expect (and welcome) issues opened
  against the repo.
