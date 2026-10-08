#!/usr/bin/env python3
"""Pairs every Lean declaration with the source lines it formalizes.

The table below is the single source of `SOURCES.md`. `check()` verifies that

* every theorem and definition in `KappaCheck/*.lean` appears in the table, and
  every name in the table exists in the Lean files;
* every cited line range exists and still contains its quoted anchor text;
* every cited certificate value equals the literal written in the Lean
  declaration, and that literal occurs in the declaration.

Run `python3 formal/lean/sources.py` to check, `--write` to regenerate SOURCES.md.
"""
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
LEAN = Path(__file__).resolve().parent
COMMIT = '6e564879f51ae16f23d392e9e196c605f36d90df'


@dataclass(frozen=True)
class Line:
    """Lines `first..last` of `path` contain `anchor` (whitespace-normalized)."""
    path: str
    first: int
    last: int
    anchor: str


@dataclass(frozen=True)
class Key:
    """Certificate value at `keys` equals the Lean literal `lean`."""
    path: str
    keys: tuple
    lean: str


NC = 'notes/compact-control-note.tex'
NI = 'notes/independent-complex.tex'
NG = 'notes/compact-control-guard.tex'
NL = 'notes/compact-control-layout.tex'
NM = 'notes/compact-control-movement.tex'
NPC = 'notes/paired-construction.tex'
NPP = 'notes/parameter-note.tex'
NNA = 'notes/nonadjacent-axis-note.tex'
NPN = 'notes/paired-note.tex'
P3 = 'upstream/build/sections/03-motifs.tex'
P5 = 'upstream/build/sections/05-layers.tex'
P8 = 'upstream/build/sections/08-assembly.tex'
CJ = 'certificates/compact-control-layer.json'
PJ = 'certificates/paired-network.json'
QJ = 'certificates/parameters.json'
NCC = 'notes/copied-centers-lemma.tex'
SCC = 'research/swapnil-parallel/upstream/notes/copied-centres.tex'
RV2 = 'docs/research/community-round2-review.md'


ARJ = 'research/matrix-exponent-synthesis/candidate/arithmetic.json'
CCN = 'certificates/copied-centers-network.json'
MES = 'research/matrix-exponent-synthesis/matrix-exponent-synthesis.tex'
BA = 'research/copied-fixed-reversed/balanced_assembly.py'
BFM = 'scripts/experiments/binary_frame_math.py'
NCX = 'notes/copied-centers-complex.tex'


def J(path, *keys):
    """Key whose Lean literal is the certificate value written as `a / b`."""
    x = json.loads((ROOT/path).read_text())
    for k in keys:
        x = x[k]
    v = Fraction(str(x))
    return Key(path, keys, str(v.numerator) if v.denominator == 1 else f'{v.numerator} / {v.denominator}')


def ASM(*keys):
    return J(ARJ, 'assembly', *keys)


SLACKS = list(json.loads((ROOT/ARJ).read_text())['assembly']['constraints'])
MARGINS = ['g1', 'g2', 'g3', 'g4', 'g5', 'g6', 'g7']


def main_(*k):
    return ('main',)+k


ROWS = [
    # -- Network.lean: the paper's count formulas ---------------------------
    ('Network', ['v', 'N', 'm'], 'v = C(h,3), N = v³, m = h³',
     [Line(P3, 16, 17, r'v=\binom h3'), Line(P3, 16, 17, r'N=v^3'),
      Line(P3, 16, 17, r'm=h^3'), Line(NI, 8, 8, r'm_{\rm c}=15625')], ''),
    ('Network', ['I'], 'I = 3v² invocations',
     [Line(P3, 31, 37, r'there are $v^2$ separate invocations at each stage'),
      Line(P3, 37, 37, r'I=3v^2')], ''),
    ('Network', ['zb', 'zc'], 'z_b = 3·C(h−3,2), z_c = C(h−3,3) + 3(h−3)',
     [Line(P3, 130, 131, r'z_{\rm b}=3\binom{97}{2}'),
      Line(P3, 130, 131, r'z_{\rm c}=\binom{97}{3}+3\cdot97'),
      Line(NI, 15, 15, r'z_{\rm c}=\binom{22}{3}+66')],
     'The paper and the note give only the h = 100 and h = 25 instances (97 = h−3, 22 = h−3); '
     'the general-h form is inferred and cross-checked at h = 25, 46, 100.'),
    ('Network', ['Wb', 'Wc'], 'W = 2N + I(vz + c), c_b = h, c_c = h + 1',
     [Line(P3, 136, 136, r'$c_{\rm b}=100$ and $c_{\rm c}=101$'),
      Line(P3, 139, 141, r'W_{\rm b}&=2N+I(vz_{\rm b}+c_{\rm b})'),
      Line(P3, 139, 141, r'W_{\rm c}&=2N+I(vz_{\rm c}+c_{\rm c})'),
      Line(NI, 14, 14, r'W_{\rm c}=2v_{\rm c}^3+3v_{\rm c}^2(v_{\rm c}z_{\rm c}+26)')],
     'c_b = h, c_c = h + 1 inferred from 100/101 at h = 100 and 26 at h = 25.'),
    ('Network', ['Lb', 'Lc'], 'L = I·c·h',
     [Line(P3, 354, 357, r'L=Ich'), Line(NI, 15, 15, r'L_{\rm c}=3v_{\rm c}^2\cdot25\cdot26')], ''),
    ('Network', ['sb', 'sc'], 's_b = W m − N + 2L, s_c = W m − 2N + 2L',
     [Line(P3, 505, 505, r'=W_{\rm b}m-N+2L_{\rm b}'),
      Line(P3, 576, 576, r's_{\rm c}=W_{\rm c}m-2N+2L_{\rm c}'),
      Line(NI, 42, 42, r's_{\rm c}=W_{\rm c}m_{\rm c}-2N_{\rm c}+2L_{\rm c}')],
     'Written as W m + 2L − N in ℕ; `sb_eq`/`sc_eq` prove it equals the ℤ form.'),
    ('Network', ['paper_h100'], 'the paper\'s h = 100 counts',
     [Line(P3, 16, 16, r'v=\binom h3=161700'), Line(P3, 37, 37, '78440670000'),
      Line(P3, 130, 131, '13968'), Line(P3, 130, 131, '147731'),
      Line(P3, 139, 142, '177176569091445000000'),
      Line(P3, 139, 142, '1873807244643542670000'),
      Line(P3, 505, 506, '177176569088785861287000000'),
      Line(P3, 576, 577, '1873807244636671267308000000')], ''),
    ('Network', ['paper_h100_deficits'], 'the paper\'s η_b, η_c at h = 100',
     [Line(P3, 673, 678, r'\frac{339}{22587335000000}'),
      Line(P3, 673, 678, r'\frac{73}{19906842167500}')], ''),
    ('Network', ['parameter_note_h46'], 'the h = 46 counts',
     [Line(NPP, 216, 218, 'm=97336'),
      Key(QJ, ('networks', 'improved_h46', 'counts', 'Wb'), '28434979789999200'),
      Key(QJ, ('networks', 'improved_h46', 'counts', 'Wc'), '130865855373752400'),
      Key(QJ, ('networks', 'improved_h46', 'counts', 'sb'), '2767747192266968049600'),
      Key(QJ, ('networks', 'improved_h46', 'counts', 'sc'), '12737958894652805035200'),
      Key(QJ, ('networks', 'improved_h46', 'counts', 'Lb'), '1462784875200'),
      Key(QJ, ('networks', 'improved_h46', 'counts', 'Lc'), '1494584546400')],
     'Not used by the κ = 83/10¹² chain; a third data point for the formulas.'),
    ('Network', ['parameter_note_h46_deficits'], 'η_b = 9/43518487588, η_c = 7/22253827054',
     [Line(NPP, 218, 219, r'\eta_b=\frac9{43518487588}'),
      Line(NPP, 218, 219, r'\eta_c=\frac7{22253827054}')], ''),
    ('Network', ['costX', 'costY'], 'data-wire residual dimensions per stage',
     [Line(P3, 378, 379, r'X:\ 2\to3&P\otimes t_X^\perp&h-1'),
      Line(P3, 382, 384, r'Y:\ 4\to5&P\otimes t_Y^\perp&h-1')],
     'Rows X: in→2, 2→3 and Y: 0→1, 4→5 of the residual table; other data edges have residual 0.'),
    ('Network', ['costCenter', 'costSide'], 'central- and side-wire residual dimensions',
     [Line(P3, 385, 388, r'\mathrm{center}:\ 3\to4&P\otimes F&h'),
      Line(P3, 389, 393, r'\mathrm{side}:\ 2\to5&P\otimes\langle t_X,t_Y\rangle^\perp&h-2'),
      Line(P3, 394, 395, r'ah(f-1)')], ''),
    ('Network', ['data_wires'], 'X grows 1 → h³ (+1 source projection); Y grows 0 → h³ − 1',
     [Line(P3, 289, 291, r'At stage 1 they start at $U_a$ on $X_a$'),
      Line(P3, 367, 367, r'Write $a=\dim A=h^{j-1}$ and $f=h^{3-j}$')], ''),
    ('Network', ['scratch_wires'], 'a central wire costs m + 2h, a side wire m',
     [Line(P3, 385, 395, r'\mathrm{center}:\ \mathrm{source}\to1&B\otimes F&(a-1)h'),
      Line(P3, 415, 416, r'Label dimension is nondecreasing along every edge except center $3\to4$')], ''),
    ('Network', ['rank_sums'], 'summing per-wire costs gives W m − N + 2L and W m − 2N + 2L',
     [Line(P3, 356, 360, r'=Wm-2N+2L'),
      Line(P3, 420, 425, r'replacing signed changes by absolute changes adds $2L$'),
      Line(P3, 500, 505, r'=W_{\rm b}m-N+2L_{\rm b}')], ''),
    ('Network', ['sb_eq', 'sc_eq'], 'the ℕ closed forms equal the paper\'s',
     [Line(P3, 505, 505, r'=W_{\rm b}m-N+2L_{\rm b}'),
      Line(P3, 576, 576, r's_{\rm c}=W_{\rm c}m-2N+2L_{\rm c}')], ''),
    # -- Certificates.lean ------------------------------------------------
    ('Certificates', ['exponent_certificate'], 'x·L ≤ η, log m < L ⇒ m(1 − η) < m^(1−x)',
     [Line(P3, 686, 691, r'm\exp(-2^{-50}\log m)'),
      Line(NI, 50, 51, r'The inequality $e^{-x}>1-x$ then yields'),
      Line(NPC, 164, 164, r'The inequality $e^{-x}>1-x$ therefore proves')], ''),
    # -- CrocSwap.lean A: complex network h = 25 ---------------------------
    ('CrocSwap', ['log_le_of_pow', 'log_split', 'L25', 'log_15625'],
     'helper: log 15625 < L25 ≈ 9.6566', [], 'Helper, sharper than the note; no source line.'),
    ('CrocSwap', ['log_15625_note'], 'log m_c < 966/100',
     [Line(NI, 49, 49, r'\log m_{\rm c}<966/100')], ''),
    ('CrocSwap', ['complex25_counts'], 'h = 25 counts and L_c < N_c',
     [Line(NI, 8, 8, r'N_{\rm c}=12167000000'), Line(NI, 11, 11, r'W_{\rm c}=58645352620000'),
      Line(NI, 11, 12, r's_{\rm c}=916333630984500000'),
      Line(NI, 11, 11, r'L_{\rm c}=10315500000'), Line(NI, 46, 46, r'$L_{\rm c}<N_{\rm c}$'),
      Key(CJ, ('complex_counts', 'Wc'), '58645352620000'),
      Key(CJ, ('complex_counts', 'sc'), '916333630984500000'),
      Key(CJ, ('complex_counts', 'Lc'), '10315500000'),
      Key(CJ, ('complex_counts', 'N'), '12167000000')], ''),
    ('CrocSwap', ['complex25_eta'], 'η_c = 14/3464399375',
     [Line(NI, 42, 44, r'=\frac{14}{3464399375}>0'),
      Key(CJ, ('complex_counts', 'eta_c'), '14 / 3464399375')], ''),
    ('CrocSwap', ['complex25_exponent'], 's_c/W_c < 15625^σ, 1 − σ = 418/10¹²',
     [Line(NI, 20, 21, r'$\sigma=1-418/10^{12}$'),
      Line(NI, 49, 51, r'$\eta_{\rm c}>(418/10^{12})(966/100)$')], ''),
    # -- B: paired bit network h = 50 ---------------------------------------
    ('CrocSwap', ['log_125000'], 'log 125000 < L₀ = 11737/1000',
     [Line(NPC, 151, 151, r'$L_0=11737/1000$'), Line(NPC, 162, 162, r'<L_0'),
      Key(PJ, ('log_m_upper',), '11737 / 1000')],
     'Proved with log 2 and log y ≤ y − 1 rather than the note\'s series S(x).'),
    ('CrocSwap', ['R50'], 'R = 509194 side roles per invocation',
     [Line(NPC, 63, 63, r'c+q=509194'),
      Key(PJ, ('bit_counts', 'side_roles_per_invocation'), '509194')],
     'Taken as given: produced by the circuit, not re-derived in Lean.'),
    ('CrocSwap', ['Wp', 'Lp', 'Dp', 'sp'], 'W = 2N + 2v²(R + h), L = 3v²h², s = W m − N + 6v²h²',
     [Line(NPC, 134, 134, r'=2N+2v^2(R+h)'),
      Line(NPC, 135, 135, r'=W_{\rm b}^{\rm pair}m-N+6v^2h^2'),
      Line(NPC, 141, 142, r'The total decreasing dimension is $3v^2h^2$')],
     'Lean writes s = W m − D with D = N − 2L, the same as line 135.'),
    ('CrocSwap', ['bit50_counts'], 'h = 50 counts',
     [Line(NPC, 3, 3, r'v=\binom h3=19600'), Line(NPC, 3, 3, r'm=h^3=125000'),
      Line(NPC, 134, 134, '406321422080000'), Line(NPC, 136, 136, '50790175992864000000'),
      Line(NPC, 137, 137, '1767136000000'),
      Key(PJ, ('bit_counts', 'W'), '406321422080000'),
      Key(PJ, ('bit_counts', 's'), '50790175992864000000'),
      Key(PJ, ('bit_counts', 'D'), '1767136000000')], ''),
    ('CrocSwap', ['bit50_eta'], 'η_b = 23/661055000',
     [Line(NPC, 154, 154, r'\frac{23}{661055000}>aL_0'),
      Key(PJ, ('bit_counts', 'eta'), '23 / 661055000')], ''),
    ('CrocSwap', ['bit50_exponent'], 's_b/W_b < 125000^τ, 1 − τ = 296/10¹¹',
     [Line(NPC, 151, 154, r'\frac{23}{661055000}>aL_0'),
      Line(NPC, 166, 166, r'\tau=1-\frac{296}{10^{11}}')], ''),
    # -- C: guard ---------------------------------------------------------
    ('CrocSwap', ['Eg', 'Bg', 'βq', 'ζq', 'C1q', 'C0n'], 'E, B, β, ζ, C₁, C₀',
     [Line(NG, 7, 7, r'E=64(W+m+1)^3,\quad B=s+E,\quad C_1=5-4\beta+\zeta'),
      Line(NG, 10, 10, r'C_0=\left\lceil\max\{128mB^2,18mB^2(1+1/\zeta)\}\right\rceil'),
      Line(NC, 69, 69, r'\beta=\frac1{1000},\quad\zeta=\frac1{10000}'),
      Line(P5, 697, 697, r'E=64(W+m+1)^3,\qquad B=s+E'),
      Key(CJ, main_('guard', 'C0'),
          '468702768364541266454706053568350325710944743089798636762052552973306387134258934583461152000000'),
      Key(CJ, main_('guard', 'zeta'), '1 / 10000'), Key(CJ, main_('guard', 'beta'), '1 / 1000')], ''),
    ('CrocSwap', ['guard_constants'], 'E, B values; 2 ≤ s < m⁵; s(8+E) ≤ 9B²; C₀ and the layer inequality',
     [Line(NG, 4, 4, r'$2\le s<m^5$'),
      Line(NG, 27, 27, r'A(e)\le s(8+E)d^{5-4\beta}\le9B^2d^{5-4\beta}'),
      Line(NG, 36, 37, r'A_{\rm layer}\le9mB^2(1+1/\zeta)d^{C_1}+18d'),
      Line(NI, 52, 52, r'$2\le s_{\rm c}<m_{\rm c}^5$'),
      Key(CJ, main_('guard', 'E'), '12908648646364723556470023518520280006040064'),
      Key(CJ, main_('guard', 'B'), '12908648646364723556470024434853910990540064'),
      Key(CJ, main_('guard', 'C1'), '49961 / 10000')],
     'Constant inequalities only; the depth recursion for A(e) is the written proof.'),
    # -- Guard.lean: the depth recursion of the guard note ---------------------
    ('Guard', ['geom_le', 'unroll', 'one_lt_log_three'], 'helpers: Σ s^i ≤ s^k, unrolling k levels, log 3 > 1',
     [Line(NG, 13, 18, r'A(e)\le sA(e/m)+E\quad\hbox{internally},\qquad A(e)\le8e')],
     'The recursion itself is the note\'s assumption, carried as hypotheses.'),
    ('Guard', ['root_bound'], 'every root e ≤ d has A(e) ≤ s(8+E)d^(5−4β)',
     [Line(NG, 23, 24, r'the number of internal levels is at most $(1-\beta)\log_m d+1$'),
      Line(NG, 26, 27, r's^j\le s d^{5(1-\beta)}'),
      Line(NG, 27, 27, r'A(e)\le s(8+E)d^{5-4\beta}'),
      Line(NG, 29, 29, r'A root that is already a leaf also satisfies this bound')],
     'For every A satisfying the two recursion hypotheses; uses 2 ≤ s < m⁵.'),
    ('Guard', ['pieces_le'], '(m−1)(1+⌊log_m d⌋) ≤ m(1+1/ζ)d^ζ',
     [Line(NG, 29, 31, r'$m(1+1/\zeta)d^\zeta$ base-$m$ pieces'),
      Line(NG, 31, 31, r'$\log d\le d^\zeta/\zeta$ and $\log m>1$'),
      Line(P5, 673, 673, r'There are at most \((m-1)(1+\lfloor\log_m d\rfloor)\) pieces')], ''),
    ('Guard', ['layer_bound'], 'A_layer ≤ 9mB²(1+1/ζ)d^C₁ + 18d ≤ C₀d^C₁',
     [Line(NG, 32, 34, r'so their depth is at most $8d$'),
      Line(NG, 33, 34, r'add at most $\lfloor D/2\rfloor+9$ units'),
      Line(NG, 36, 37, r'A_{\rm layer}\le9mB^2(1+1/\zeta)d^{C_1}+18d \le C_0d^{C_1}')],
     'Pieces, individual axes and outer phases are composed sequentially, so depths add.'),
    ('Guard', ['guard_instance'], 'the h = 25, β = 1/1000, ζ = 1/10000 instance',
     [Line(NG, 4, 4, r'Assume $m\ge3$ and $2\le s<m^5$'),
      Line(NC, 69, 69, r'\beta=\frac1{1000},\quad\zeta=\frac1{10000}')],
     'All constant hypotheses discharged by `guard_constants`.'),
    # -- Frames.lean: the paired circuit's label algebra --------------------
    ('Frames', ['form', 'ind', 'sum_ind', 'sum_ind_mul'], 'the form I − J/9 and triple indicators',
     [Line(NPC, 88, 88, r'Use the original rational form $I-J/9$ on $F=\mathbb Q^{50}$')],
     'Stated for every h.'),
    ('Frames', ['form_ind', 'neighbors_orthogonal'], 'B(t_S, t_T) = |S ∩ T| − 1, so neighbors are orthogonal',
     [Line(NPC, 101, 102, r'has $U_z\subset t_T^\perp$, because every contributing triple is a neighbor')],
     'With the checker\'s exact output supports, this gives U_z ⊂ t_T^⊥.'),
    ('Frames', ['common', 'span_le_common', 'form_self_common', 'form_pos_common', 'label_anisotropic'],
     'spans through a common point satisfy Σu = 3uᵢ and B(u,u) = Σ_{j≠i} uⱼ² > 0',
     [Line(NPC, 93, 94, r'Every retained node is a sum from an original common-point group'),
      Line(NPC, 96, 97, r'\sum_j u_j=3u_i,\qquad \langle u,u\rangle=\sum_{j\ne i}u_j^2>0\quad(u\ne0)'),
      Line(NPC, 99, 99, r'Thus $U_z$ is nondegenerate')],
     'The common point of every node is checked on the exported circuit (rcheck).'),
    # -- Movement.lean: the compact-control address algebra -------------------
    ('Movement', ['bxor', 'four_step', 'four_step_parity'], 'the four-step update toggles the parity by z and restores w',
     [Line(NM, 47, 52, r'v\gets v+2zw,\qquad w\gets w+(v\bmod2),\qquad v\gets v+z(1-2w),\qquad w\gets w-((v\bmod2)\mathbin\oplus z)'),
      Line(NM, 53, 55, r'The final values are $v+z(1-2a)$ and the original $w$')], ''),
    ('Movement', ['later_source'], 'two passes with parities u mod 2 and (u+x) mod 2 toggle by x',
     [Line(NM, 72, 78, r'the two control parities differ by exactly $x_{j_i}$')], ''),
    ('Movement', ['guard_no_carry'], 'the guard interval keeps a displaced segment in [0, 2^K)',
     [Line(NM, 86, 89, r'2B\le g_i<2^{K-1}-2B'),
      Line(NM, 91, 94, r'The conservative guard interval therefore prevents every carry or borrow')], ''),
    ('Movement', ['digits_lt', 'digit_extract', 'packed_rotation'],
     'under the guard, one packed rotation updates each segment independently',
     [Line(NM, 57, 63, r'A target-slot update is one modular rotation of $y$'),
      Line(NM, 91, 94, r'prevents every carry or borrow between the wide segments')],
     'Digit-level arithmetic only; the streaming rotation itself is not modelled.'),
    ('Movement', ['repair_permutation'], 'S = T off a T-invariant bad set ⇒ TS⁻¹ fixes good addresses and permutes the bad set',
     [Line(NM, 104, 108, r'Since $S=T$ off the bad set, $S$ preserves that set too'),
      Line(NM, 118, 119, r'because $TS^{-1}$ permutes the bad set')], ''),
    # -- Layout.lean: row arithmetic -------------------------------------------
    ('Layout', ['row_range'], 'R_row = 2^(q₀K) ≥ W^k₀',
     [Line(NL, 10, 11, r'q_0=\lceil\log_2W\rceil\lceil\log_m(2d)\rceil, \quad k_0=\lceil\log_m d\rceil'),
      Line(NL, 30, 30, r'$R_{\rm row}=2^{q_0K}\ge W^{k_0}$')],
     'Hypotheses W ≤ 2^⌈log₂W⌉ and ⌈log_m d⌉ ≤ ⌈log_m 2d⌉ are left to the caller.'),
    ('Layout', ['pad'], 'padding to a multiple of W^k₀ at most doubles the rows',
     [Line(NL, 31, 35, r'increases total volume by at most two')], ''),
    ('Layout', ['role_rows', 'split_invariant'], 'u = Wg + w gives each role 1/W of the rows; divisibility survives',
     [Line(NL, 37, 37, r'write the row index as $u=Wg+w$, $0\le w<W$'),
      Line(NL, 40, 41, r'exactly $1/W$ of the parent volume'),
      Line(NL, 41, 41, r'At depth $j$ the remaining row count is divisible by $W^{k_0-j}$')], ''),
    ('Layout', ['reserved_axes'], 'q_F + q_B ≤ 3dG/K + 2 ≤ 6d^(1−c)G + 2',
     [Line(NL, 5, 7, r'H=dG'), Line(NL, 65, 67, r'q_F+q_B\le\frac{3dG}{K}+2\le6d^{1-c}G+2')], ''),
    # -- CopiedCentres.lean: the copied-centre lemma -------------------------------
    ('CopiedCentres', ['move', 'move_frame', 'move_move', 'gate_frame'], 'frame changes and pointwise gates on physical streams',
     [Line(NCC, 23, 27, r'Changing a copy from frame $Q_1$ to $Q_2$ means applying $\mathcal F_{Q_2}\mathcal F_{Q_1}^{-1}$ to its physical stream')],
     'The address frames are modelled as arbitrary linear equivalences.'),
    ('CopiedCentres', ['directOld', 'directCopied', 'direct_same', 'direct_action'],
     'direct centres: the copied word gives the same streams, y += lkx, and restores any dirty centre',
     [Line(SCC, 14, 17, r"So the centre's frame path is $D_0\to D_1\to D_0\to D_1$"),
      Line(SCC, 20, 23, r'The scalar action, the endpoints of every role and the restoration of arbitrary scratch are unchanged')], ''),
    ('CopiedCentres', ['forwardOld', 'forwardCopied', 'forward_same'],
     'retained centres, forward: copy D_U → D₀ for the reads, original D_U → D₁',
     [Line(NCC, 45, 56, r'Keep the original at $D_U$, copy its physical stream, and transform only the copy to $D_0$, paying rank $r$')],
     'The cleanup is an arbitrary continuation of the original stream.'),
    ('CopiedCentres', ['reverseOld', 'reverseCopied', 'reverse_same'],
     'retained centres, reverse: original D₀ → D_{U⊥}, copy D_{U⊥} → D₁ for the reads',
     [Line(NCC, 58, 66, r'advance the original directly to $D_{U^\perp}=D_0\mathbin{\perp}(P\otimes U^\perp)$, paying $h-r$')], ''),
    ('CopiedCentres', ['charge', 'finrank_sup_of_disjoint', 'Frames', 'Frames.DU', 'Frames.DUp', 'Frames.D₁',
                       'Frames.hU', 'Frames.hUp', 'Frames.dim_EUp', 'Frames.dim_DU', 'Frames.dim_DUp',
                       'Frames.dim_D₁', 'Frames.nested'],
     'frames D_U = D₀ ⊕ (P⊗U), D_{U⊥} = D₀ ⊕ (P⊗U⊥), D₁ = D₀ ⊕ (P⊗F) with P⊗F = P⊗U ⊕ P⊗U⊥; dim U⊥ = h − r derived',
     [Line(NCC, 15, 22, r'Thus a local change of rank $d$ has ambient rank $d$')], ''),
    ('CopiedCentres', ['forward_profile', 'reverse_profile'], 'every charge: profile z^r + z^h becomes z^r + z^(h−r), both orientations',
     [Line(NCC, 37, 43, r'can be changed from $z^r+z^h$ to $z^r+z^{h-r}$')], ''),
    ('CopiedCentres', ['Frames.new_residual'], 'the original\'s new edge has residual P⊗U⊥ (its basis is the note\'s unproved claim)',
     [Line(NCC, 68, 71, r'the direct original growth uses $C_{U^\perp}$')],
     'Lean proves the residual is P⊗U⊥, not that it has the required basis.'),
    ('CopiedCentres', ['witness', 'witness_dims', 'witness_profiles'], 'non-vacuity: a frame system with r = 1, h = 2',
     [], 'Shows the frame hypotheses are satisfiable with 0 < r < h; no source line.'),
    ('CopiedCentres', ['direct_profile'], 'direct centres: each move charges h, so three rank-h children become two',
     [Line(SCC, 22, 24, r'Each centre then has two children of width $h$ per stage instead of three')], ''),
    ('CopiedCentres', ['histogram_update'], 'H′₁ = H₁ + h, H′_h = H_h − h: rank mass drops by h(h−1)',
     [Line(NCC, 79, 86, r"H'_{h,1}=H_{h,1}+h,\qquad H'_{h,h}=H_{h,h}-h")], ''),
    ('CopiedCentres', ['updated', 'copied_mass'], 'summing the histogram update over invocations: s = Wm − N + L, Wm − s = N − L',
     [Line(NCC, 92, 100, r's=Wm-N+L,\qquad Wm-s=N-L'),
      Line(SCC, 42, 42, r'The deficit is now $Wm-s=N-L=v(v-2h^2)$')], ''),
    ('CopiedCentres', ['selected_network'], 'the selected (23,25) network: N, W from the role counts, L, deficit and total rank',
     [Line(RV2, 89, 91, r'L=2,226,400; total rank=78,860,441,550; deficit Wm−s=1,846,900')], ''),
    ('CopiedCentres', ['direct_deficit', 'retained_totals_deficit'], 'Swapnil round six: deficits at h = 25 and h = 23',
     [Line(SCC, 42, 42, r'$Wm-s=N-L=v(v-2h^2)$'),
      Line(SCC, 48, 49, r'so the loss per centre is $h-1$')],
     'The h = 23 deficit equals that of lean/Round6.lean\'s bit histogram.'),
    # -- D: parameters, slacks, margins ------------------------------------
    ('CrocSwap', ['τ', 'σ', 'ε', 'c', 'lam', 'lamp', 'κ', 'β', 'δ', 'C1'], 'the chosen parameters',
     [Line(NC, 68, 68, r'\epsilon=\frac{1999}{10000},\quad c=\frac15'),
      Line(NC, 69, 69, r'\delta=\frac1{10^6}'), Line(NC, 70, 70, r'C_1=\frac{49961}{10000}'),
      Line(NC, 71, 71, r'\lambda=1-\frac{1671}{4\cdot10^{12}}'),
      Line(NC, 72, 72, r"\lambda'=1-\frac{167}{4\cdot10^{11}}"),
      Line(NC, 73, 73, r'\kappa=\frac{83}{10^{12}}'),
      Key(CJ, main_('parameters', 'tau'), '12499999963 / 12500000000'),
      Key(CJ, main_('parameters', 'sigma'), '499999999791 / 500000000000'),
      Key(CJ, main_('parameters', 'epsilon'), '1999 / 10000'),
      Key(CJ, main_('parameters', 'c'), '1 / 5'),
      Key(CJ, main_('parameters', 'lam'), '3999999998329 / 4000000000000'),
      Key(CJ, main_('parameters', 'lamp'), '399999999833 / 400000000000'),
      Key(CJ, main_('parameters', 'kappa'), '83 / 1000000000000'),
      Key(CJ, main_('parameters', 'beta'), '1 / 1000'),
      Key(CJ, main_('parameters', 'delta'), '1 / 1000000'),
      Key(CJ, main_('parameters', 'C1'), '49961 / 10000')], ''),
    ('CrocSwap', ['parameter_origin'], 'τ = 1 − a, σ = 1 − a_c, C₁ from the guard',
     [Line(NC, 65, 65, r'Put $a=296/10^{11}$ and $a_{\rm c}=418/10^{12}$'),
      Line(NC, 67, 67, r'\tau=1-a,\quad\sigma=1-a_{\rm c}')], ''),
    ('CrocSwap', ['internal', 'leaf', 'prep', 'layer'], 'the layer exponents χ, χ_leaf, χ_reserve',
     [Line(NC, 77, 79, r'\chi=\tau+(1-\beta)(\sigma-\tau)'),
      Line(NC, 78, 78, r'\chi_{\rm leaf}=\sigma+\beta(1-\sigma)'),
      Line(NC, 79, 79, r'\chi_{\rm reserve}=1-c=\frac45'),
      Line(NL, 94, 94, r'\chi=\tau+(1-\beta)\max\{\sigma-\tau,0\}'),
      Line(NL, 71, 71, r'd^{\max\{1-c,0\}}')],
     'Lean keeps the layout note\'s max; the main note drops it because σ > τ (`exponents_below_layer`).'),
    ('CrocSwap', ['recurrence_values'], 'exact recurrence exponents',
     [Key(CJ, main_('recurrence', 'internal'), '499999999789729 / 500000000000000'),
      Key(CJ, main_('recurrence', 'leaf'), '499999999791209 / 500000000000000'),
      Key(CJ, main_('recurrence', 'preprocessing'), '4 / 5'),
      Key(CJ, main_('recurrence', 'layer'), '499999999791209 / 500000000000000')], ''),
    ('CrocSwap', ['constraint_slacks'], 'all 31 constraint slacks are positive',
     [Line(NC, 81, 84, r'$\max\{\tau,\sigma,\chi\}<\lambda<\lambda\'<1$'.replace("\\'", "'")),
      Line('scripts/certify.py', 94, 94, 'def constraints('),
      Line('scripts/compact_control_layer.py', 86, 87, "slacks['reserved_axes']=p.lamp-e['preprocessing']")],
     'The 31-entry list is the script\'s `constraints(...)`, not a note display.'),
    ('CrocSwap', ['slack_values'], 'the certificate\'s slack values are exact',
     [Key(CJ, main_('constraint_slacks', 'packed_overhead'), '349 / 125000000000000'),
      Key(CJ, main_('constraint_slacks', 'reserved_axes'), '79999999833 / 400000000000'),
      Key(CJ, main_('constraint_slacks', 'guard_width'), '127961 / 100000000'),
      Key(CJ, main_('constraint_slacks', 'leaf_cost'), '41 / 500000000000000'),
      Key(CJ, main_('constraint_slacks', 'lambda_prime_above_lambda'), '1 / 4000000000000'),
      Key(CJ, main_('constraint_slacks', 'lambda_above_sigma'), '1 / 4000000000000'),
      Key(CJ, main_('constraint_slacks', 'lambda_above_tau'), '10169 / 4000000000000'),
      Key(CJ, main_('constraint_slacks', 'gaussian_cost'), '31 / 250000'),
      Key(CJ, main_('constraint_slacks', 'lambda_below_one'), '1671 / 4000000000000'),
      Key(CJ, main_('constraint_slacks', 'lambda_prime_below_one'), '167 / 400000000000'),
      Key(CJ, main_('constraint_slacks', 'dimension_upper_bound'), '4003 / 30000'),
      Key(CJ, main_('constraint_slacks', 'crt_layout'), '296037 / 125000000000000'),
      Key(CJ, main_('constraint_slacks', 'prefix_cost'), '19003 / 25000'),
      Key(CJ, main_('constraint_slacks', 'scalar_cost'), '800099 / 1000000'),
      Key(CJ, main_('constraint_slacks', 'delta_below_one_eighth'), '124999 / 1000000'),
      Key(CJ, main_('constraint_slacks', 'prime_interval_growth'), '3001 / 5000'),
      Key(CJ, main_('constraint_slacks', 'alpha_below_sqrt_p'), '8001 / 40000'),
      Key(CJ, main_('constraint_slacks', 'gamma_sublinear'), '4003 / 20000'),
      Key(CJ, main_('constraint_slacks', 'K_smaller_than_ell'), '19003 / 25000'),
      Key(CJ, main_('constraint_slacks', 'K_dominates_log_p'), '1999 / 50000'),
      Key(CJ, main_('constraint_slacks', 'r_superpolynomial'), '8001 / 10000'),
      Key(CJ, main_('constraint_slacks', 'tau_below_one'), '37 / 12500000000'),
      Key(CJ, main_('constraint_slacks', 'sigma_below_one'), '209 / 500000000000'),
      Key(CJ, main_('constraint_slacks', 'beta_below_one'), '999 / 1000')], ''),
    ('CrocSwap', ['g1', 'g2', 'g3', 'g4', 'g5', 'g6', 'g7'], 'the seven margins',
     [Line(NC, 104, 104, r'g_1&=1-\epsilon(1+c),&g_2&=\epsilon c(1-\tau)'),
      Line(NC, 105, 105, r"g_3&=\epsilon(1-\lambda'),&g_4&=(1-\tau)(1-\epsilon)"),
      Line(NC, 106, 106, r'g_5&=1/4-\delta-5\epsilon/4,&g_6&=1-\delta-\epsilon,\qquad g_7=\epsilon'),
      Line(P8, 856, 857, r'g_4&=1-\tau-\epsilon(2-\tau)'),
      Line(P8, 856, 857, r'g_5=1/4-\delta-3\epsilon/2'),
      Line(NNA, 124, 124, r'g_4=(1-\tau)(1-\epsilon)'),
      Line(NPN, 55, 56, r'normalized exponent $3/4+\delta+5\epsilon/4$')],
     'g₄ and g₅ differ from the paper on purpose: nonadjacent routing (g₄) and the smaller Gaussian width (g₅).'),
    ('CrocSwap', ['margin_values'], 'exact margin values',
     [Key(CJ, main_('margins', 'g1'), '19003 / 25000'),
      Key(CJ, main_('margins', 'g2'), '73963 / 625000000000000'),
      Key(CJ, main_('margins', 'g3'), '333833 / 4000000000000000'),
      Key(CJ, main_('margins', 'g4'), '296037 / 125000000000000'),
      Key(CJ, main_('margins', 'g5'), '31 / 250000'),
      Key(CJ, main_('margins', 'g6'), '800099 / 1000000'),
      Key(CJ, main_('margins', 'g7'), '1999 / 10000')], ''),
    ('CrocSwap', ['kappa_witness'], 'min g = g₃ > κ, gap 1833/(4·10¹⁵), 2⁻³⁴ < κ < 2⁻³³',
     [Line(NC, 111, 111, r'G_*:=\min_i g_i=g_3=\frac{333833}{4\cdot10^{15}}'),
      Line(NC, 112, 112, r'G_*-\kappa=\frac{1833}{4\cdot10^{15}}>0'),
      Line(NC, 118, 118, r'2^{-34}<\frac{83}{10^{12}}<2^{-33}'),
      Key(CJ, main_('absorption_gap'), '1833 / 4000000000000000')], ''),
    # -- E: repair ----------------------------------------------------------
    ('CrocSwap', ['repair_bound'], 'n(2·2⁻ᴳ + 8·2ᴳ⁻ᴷ) ≤ 5/(128p³) for every p ≥ 2',
     [Line(NM, 101, 101, r'\delta=\min\{1,n(2\cdot2^{-G}+8\cdot2^{G-K})\}'),
      Line(NM, 149, 150, r'$K\ge G+4\ell_p+10$'),
      Line(NM, 152, 152, r'\delta\le \frac{5}{128p^3}'),
      Line(NL, 5, 5, r'G=4\lceil\log_2p\rceil+6'),
      Line(NL, 24, 24, r'nG=(f-1)G\le H')],
     'ℓ_p = Nat.size(p − 1) = ⌈log₂p⌉ for p ≥ 2. Bounds the second argument of the min. '
     'n ≤ p follows from n ≤ d (layout line 24, H = dG).'),
    # -- F: recurrence levels -------------------------------------------------
    ('CrocSwap', ['internal_level'], 'level i costs at most d^χ',
     [Line(NL, 90, 91, r'O(G^\tau e^\tau(b/m^\tau)^j)'),
      Line(NL, 93, 98, r'otherwise the'),
      Line(P5, 654, 657, r'Since \(a\le m^\sigma<m^\lambda\)')], ''),
    ('CrocSwap', ['leaf_level'], 'leaves cost at most d^(σ + β(1−σ))',
     [Line(NL, 99, 100, r'$O(d^{\sigma+\beta(1-\sigma)})$'),
      Line(P5, 663, 667, r'\(a^j\le m^{j\sigma}=(e/u)^\sigma\)')], ''),
    ('CrocSwap', ['exponents_below_layer'], 'τ < σ, χ < λ, χ_leaf < λ′, λ < λ′',
     [Line(NC, 82, 83, r"$\max\{\chi_{\rm leaf},\chi_{\rm reserve}\}<\lambda'$"),
      Line(NL, 112, 113, r"\max\{\sigma+\beta(1-\sigma),1-c,0\}<\lambda'")], ''),
    ('CrocSwap', ['note_parameter_lines'], 'the note\'s displayed parameter comparisons',
     [Line(NC, 79, 79, r'\chi_{\rm reserve}=1-c=\frac45'),
      Line(NC, 82, 82, r"$\max\{\tau,\sigma,\chi\}<\lambda<\lambda'<1$"),
      Line(NC, 84, 84, r'$\epsilon C_1=99872039/10^8<1$'),
      Line(NC, 91, 92, r'\alpha=\Theta(p^{11999/40000})'),
      Line(NC, 91, 92, r'\gamma=O(p^{15997/20000})'),
      Line(NC, 95, 95, r'indeed $184<2^8$'),
      Line(NC, 96, 96, r'$1-2\epsilon=3001/5000>0$'),
      Line(NC, 98, 98, r'$\epsilon(1+c)<1$')], ''),
    ('CrocSwap', ['gaussian_cutoff_general'], 'every 0 ≤ ε ≤ 1/5: b ≥ 2⁴⁰ ⇒ 46 b^((1+3ε)/2) ≤ b/4',
     [Line(NC, 94, 95, r'Since $\epsilon<1/5$, $b\ge2^{40}$ implies $46b^{(1+3\epsilon)/2}\le b/4$')], ''),
    ('CrocSwap', ['gaussian_cutoff'], 'b ≥ 2⁴⁰ ⇒ 46 b^((1+3ε)/2) ≤ b/4',
     [Line(NC, 94, 95, r'Since $\epsilon<1/5$, $b\ge2^{40}$ implies $46b^{(1+3\epsilon)/2}\le b/4$')], ''),
    # -- G, H: the scoped ceiling ----------------------------------------------
    ('CrocSwap', ['kappa_lt_fifth'], 'Gaussian and leaf margins force κ < (1 − σ)/5',
     [Line(NC, 140, 142, r'Gaussian margin forces $\epsilon<1/5$'),
      Line(NC, 142, 142, r"$1-\lambda'<(1-\beta)(1-\sigma)<1-\sigma$"),
      Line(NC, 145, 145, r'\kappa<\frac{a_{\rm c}^{\rm actual}}5')], ''),
    ('CrocSwap', ['certified_saving_le', 'log_15625_gt', 'scoped_ceiling'],
     'coarse form: κ < 2⁻³³ for every admissible choice',
     [Line(NC, 143, 146, r'<8.369598075\cdot10^{-11}<2^{-33}')],
     'Superseded by `scoped_ceiling_exact`; kept as an independent coarse check.'),
    ('CrocSwap', ['ps', 'neglog_bounds', 'log5_identity', 'Llo', 'log_15625_ge', 'Nhi',
                  'neglog_eta_le', 'enclosure_le_U', 'certified_saving_log'],
     'helpers: 26-digit enclosures of log 15625 and −log(1 − η_c)',
     [Line(NC, 139, 140, r'approximately $4.1847990372\cdot10^{-10}$')],
     'Helpers; Nhi/Llo is the note\'s saving enclosure.'),
    ('CrocSwap', ['enclosure_gt_U_shrunk'], 'negative control: the enclosure exceeds U·(1 − 10⁻²⁴)',
     [], 'Shows the check against U is tight; no source line.'),
    ('CrocSwap', ['ηc'], 'η_c as a real', [Line(NI, 44, 44, r'=\frac{14}{3464399375}>0')], ''),
    ('CrocSwap', ['Uceil'], 'the certificate\'s exact ceiling U',
     [Key(CJ, ('scoped_ceiling', 'upper'), '__UCEIL__')], ''),
    ('CrocSwap', ['scoped_ceiling_exact'], 'κ < U for every admissible choice with this motif',
     [Line(NC, 143, 146, r'\kappa<\frac{a_{\rm c}^{\rm actual}}5'),
      Line(NC, 146, 146, r'<8.369598075\cdot10^{-11}')], ''),
    ('CrocSwap', ['ceiling_facts'], 'U < 8.369598075·10⁻¹¹ < 2⁻³³; κ > 0.99 U',
     [Line(NC, 146, 146, r'<8.369598075\cdot10^{-11}<2^{-33}'),
      Line(NC, 148, 148, r'The displayed witness exceeds 99\% of this upper enclosure')], ''),
    ('CrocSwap', ['witness_meets_ceiling'], 'their witness satisfies every hypothesis',
     [], 'Non-vacuity check for `scoped_ceiling_exact`; no source line.'),
    # -- Selected.lean: main's selected witness κ = 25508460085039/5·10¹⁷ -----------
    ('Selected', ['Φ'], 'the moment Φ(a) = (1/W) Σ_t n_t (t/m)^(1−a)',
     [Line(MES, 63, 65, r'\Phi(a)=\frac1W\sum_{t=1}^{m-1} n_t(t/m)^{1-a}<1.')], ''),
    ('Selected', ['P4', 'S5', 'exp_le_P4', 'S5_le_exp', 'rpow_split', 'term_le', 'le_term',
                  'moment_lt_one', 'one_lt_moment'],
     'exp bounds and the termwise reduction (t/m)^(1−a) = (t/m)·exp(a·log(m/t))',
     [Line(BFM, 82, 83, 'upper += weight*(1+v+v*v/(2*(1-v/3)))')],
     'Lean bounds exp by `Real.exp_bound\'` (four terms), which is below the script\'s Padé form.'),
    ('Selected', ['log_list', 'log_16_15', 'log_25_24', 'log_81_80', 'log_126_125', 'log_176_175',
                  'log_351_350', 'log_715_714', 'log_343_342', 'log_576_575', 'log_481_480'],
     'logarithms: log(n/(n−1)) by `neglog_bounds`, and log of a product of their powers',
     [Line(BFM, 53, 63, 'z = (y-1)/(y+1)')],
     'A different series from the script\'s; every log(m/t) is an integer combination of these ten.'),
    ('Selected', ['aB', 'aC'], 'the savings a_b and a_c = 717/10⁷',
     [Line(MES, 186, 186, r'a_b=\frac{102039046058023}{2000000000000000000}'),
      Line(NCX, 100, 100, r'With $a_c=717/10^7$, $\sigma=1-a_c$'),
      J(ARJ, 'bit_saving'), J(CCN, 'complex', 'saving')], ''),
    ('Selected', ['bitRows', 'cxRows'], 'the child histograms (t, n_t)',
     [Line(MES, 180, 182, r'Its physical width is 137,151,806 and total rank 78,860,441,550'),
      Line(NCX, 89, 96, r'\text{auxiliary exterior}&2B_c&756')],
     '`arithmetic.json` `source_profile.child_multiplicities` and `copied-centers-network.json` '
     '`complex.child_width_multiplicities`; `gen_selected.py --check` ties them to the JSON.'),
    ('Selected', ['bitHlo', 'bitHhi', 'bitU', 'bitD', 'cxHlo', 'cxHhi', 'cxU', 'cxD', 'bit_logs', 'cx_logs',
                  'bit_hints', 'cx_hints'],
     'per-row enclosures of log(m/t) and of exp, all rechecked in Lean', [],
     'Proof hints computed by `gen_selected.py`; no source line.'),
    ('Selected', ['bit_moment'], 'Φ_b(a_b) < 1 as a real inequality',
     [Line(MES, 63, 65, r'n_t(t/m)^{1-a}<1'), Line(MES, 183, 187, r'Finer rational moment certification')], ''),
    ('Selected', ['cx_moment'], 'Φ_c(a_c) < 1 as a real inequality',
     [Line(NCX, 103, 106, r'\frac{\sum_tn_tt^\sigma}{W_cm_c^\sigma}')], ''),
    ('Selected', ['bit_moment_tight', 'cx_moment_tight'],
     'negative controls: Φ_b(a_b + 10⁻¹⁶) > 1 and Φ_c(a_c + 10⁻⁷) > 1', [],
     'Shows each moment test is tight; no source line.'),
    ('Selected', ['IsHalvingDegree', 'bit_halving', 'cx_halving'], 'halving degrees 9 and 20',
     [Line(BA, 44, 49, 'while m**degree <= 2 * child**degree:'),
      J(ARJ, 'finite_bridge', 'bit', 'halving_degree'), J(ARJ, 'finite_bridge', 'complex', 'halving_degree')], ''),
    ('Selected', ['wire_bits'], 'role bit lengths 28 and 30; largest children 529 and 756',
     [Line(BA, 63, 63, 'W.bit_length()'), J(ARJ, 'finite_bridge', 'bit', 'maxchild'),
      J(ARJ, 'finite_bridge', 'complex', 'maxchild')], ''),
    ('Selected', ['rank_mass'], 'Σ t n_t = s: s_b = Wm − N + L and s_c',
     [Line(MES, 182, 182, r'total rank 78,860,441,550'),
      Line(NCX, 84, 84, r's_c=W_cm_c-N_c+L_c&=421548223824'), J(ARJ, 'finite_bridge', 'complex', 's')], ''),
    ('Selected', ['mC', 'WC', 'childC', 'sC', 'scalar', 'E', 'Bs', 'literal', 'C0', 'inductionGap',
                  'coefficient', 'degree', 'degreeGap'],
     'the finite-bridge constants and their formulas',
     [Line(BA, 72, 78, 'E = 64*(W+m+scalar+1)**3'), Line(BA, 87, 90, 'gap = degree-Q(51,25)*coefficient'),
      J(ARJ, 'finite_bridge', 'complex', 'scalar_group_upper'), J(ARJ, 'finite_bridge', 'rows', 'degree')],
     '`scalar_group_upper` is supplied by the producer, as in the script.'),
    ('Selected', ['semantic_values'], 'semantic and row constants, with the script\'s requirements',
     [Line(BA, 79, 80, 'require(E > literal and semantic'),
      J(ARJ, 'finite_bridge', 'semantic', 'E'), J(ARJ, 'finite_bridge', 'semantic', 'B'),
      J(ARJ, 'finite_bridge', 'semantic', 'literal_charge'), J(ARJ, 'finite_bridge', 'semantic', 'C0'),
      J(ARJ, 'finite_bridge', 'semantic', 'strict_literal_gap'),
      J(ARJ, 'finite_bridge', 'semantic', 'induction_gap'),
      J(ARJ, 'finite_bridge', 'rows', 'coefficient'), J(ARJ, 'finite_bridge', 'rows', 'degree_gap')], ''),
    ('Selected', ['κ', 'β', 'hB'], 'κ, β = 1/20 and the backoff h = 10⁻¹⁸',
     [Line(MES, 186, 190, r'\kappa=\frac{25508460085039}{500000000000000000}'),
      J(ARJ, 'kappa'), ASM('parameters', 'beta'), J(ARJ, 'h_backoff')], ''),
    ('Selected', ['τ', 'σ', 'q', 'lp', 'c', 'ε', 'lam', 'G', 'r', 'δ', 'C1'], 'the balanced parameters',
     [Line(BA, 112, 119, 'lp, c, eps = 1-q, q+h/4, (1-h)/(1+q)')], ''),
    ('Selected', ['internal', 'leaf'], 'the recurrence exponents',
     [Line(BA, 126, 127, 'internal = tau+(1-beta)*max(sigma-tau,Q(0))')], ''),
    ('Selected', MARGINS + ['margins'], 'the seven margins',
     [Line(BA, 120, 121, 'margins = dict(g1=1-eps, g2=a, g3=G, g4=a,')], ''),
    ('Selected', ['slacks', 'slacks_length'], 'the 47 slacks, by name and formula',
     [Line(BA, 128, 146, 'slacks = dict(a_positive=a, a_below_b=b-a')], ''),
    ('Selected', ['parameter_values'], 'every parameter equals the certificate\'s value',
     [ASM('parameters', k) for k in ('tau', 'sigma', 'q', 'c', 'epsilon', 'lambda_', 'lambda_prime',
                                    'alpha_squared_power', 'delta', 'kappa')], ''),
    ('Selected', ['slack_values'], 'every slack equals the certificate\'s value',
     [ASM('constraints', k) for k in SLACKS], ''),
    ('Selected', ['margin_values'], 'every margin equals the certificate\'s value',
     [ASM('margins', k) for k in MARGINS], ''),
    ('Selected', ['slacks_pos'], 'all 47 slacks are positive',
     [Line(BA, 147, 148, 'failed = {name:str(value) for name,value in slacks.items() if value <= 0}')], ''),
    ('Selected', ['kappa_below_margins'], 'the minimum margin is G = εq, and κ < G',
     [Line(BA, 149, 149, "require(min(margins.values()) == G, 'unexpected controlling margin')")], ''),
    ('Selected', ['balanced_identities'], '1 − ε − G = h, 1 − ε − r = h/2, 1 − ε(1+c) = h − εh/4',
     [Line(BA, 150, 151, "require(1-eps-G == h and 1-eps-r == h/2")], ''),
    ('Selected', ['kappa_facts'], 'κ beats the published witness and its old scoped limit; κ < a_b/(1+a_b); 2⁻¹⁵ < κ',
     [Line(MES, 192, 194, r'the new value exceeds the old scoped limit'),
      Line(BA, 156, 156, 'absorption_gap=G-kappa,scoped_limit=a/(1+a)'),
      J(ARJ, 'comparison', 'old_published_kappa'), J(ARJ, 'comparison', 'old_formal_scoped_limit'),
      ASM('scoped_limit'), ASM('absorption_gap')],
     'Negative control: κ + 2·10⁻¹⁸ (the next grid value) exceeds G.'),
    ('Selected', ['selected_certificate'], 'both moments, all 47 slacks and κ below every margin',
     [Line('README.md', 32, 35, 'The seven final exponent margins are strictly positive.')], ''),
]

DECL = re.compile(r'^(?:@\[[^\]]*\] )?(?:noncomputable )?(?:theorem|def|structure) (\S+)', re.M)
STOP = re.compile(r'^(?:@\[|theorem|def|structure|noncomputable|omit|/-|end |namespace|section)', re.M)


def lean_decls():
    out = {}
    for f in sorted((LEAN/'KappaCheck').glob('*.lean')):
        text = f.read_text()
        for match in DECL.finditer(text):
            rest = text[match.end():]
            stop = STOP.search(rest)
            out[(f.stem, match.group(1))] = (f, text.count('\n', 0, match.start())+1,
                                             match.group(0)+(rest[:stop.start()] if stop else rest))
    return out


def norm(s):
    return ' '.join(s.split())


def lean_value(literal):
    if not re.fullmatch(r'[0-9 /^]+', literal):
        raise ValueError(literal)
    a, _, b = literal.partition('/')
    ev = lambda t: eval(t.replace('^', '**')) if t.strip() else 1
    return Fraction(ev(a))/Fraction(ev(b))


def json_at(path, keys):
    x = json.loads((ROOT/path).read_text())
    for k in keys:
        x = x[k]
    return x


def check():
    errors = []
    decls = lean_decls()
    named = set()
    for module, names, _, refs, _ in ROWS:
        for name in names:
            key = (module, name)
            named.add(key)
            if key not in decls:
                errors.append(f'{module}.{name}: not found in Lean sources')
        for ref in refs:
            if isinstance(ref, Line):
                lines = (ROOT/ref.path).read_bytes().decode().split('\n')  # '\n' only, as GitHub counts
                if not 1 <= ref.first <= ref.last <= len(lines):
                    errors.append(f'{ref.path}:{ref.first}-{ref.last}: out of range')
                elif norm(ref.anchor) not in norm(' '.join(lines[ref.first-1:ref.last])):
                    errors.append(f'{ref.path}:{ref.first}-{ref.last}: anchor {ref.anchor!r} missing')
            else:
                value = Fraction(str(json_at(ref.path, ref.keys)))
                body = ' '.join(decls[(module, n)][2] for n in names if (module, n) in decls)
                literal = ref.lean
                if literal == '__UCEIL__':
                    literal = re.search(r':= ([0-9]+ / [0-9]+)', body).group(1)
                if lean_value(literal) != value:
                    errors.append(f'{ref.path} {".".join(ref.keys)}: {value} != Lean {literal}')
                elif norm(literal) not in norm(body):
                    errors.append(f'{module}.{"/".join(names)}: literal {literal} not in declaration')
    for key in sorted(set(decls)-named):
        errors.append(f'{key[0]}.{key[1]}: declaration missing from the table')
    return errors


def link(ref):
    if isinstance(ref, Key):
        return f'`{Path(ref.path).name}` `{".".join(ref.keys)}`'
    span = f'L{ref.first}' if ref.first == ref.last else f'L{ref.first}-L{ref.last}'
    label = f'{Path(ref.path).name}:{ref.first}' + ('' if ref.first == ref.last else f'–{ref.last}')
    return f'[{label}](../../{ref.path}#{span})'


def render():
    decls = lean_decls()
    out = ['# Lean declarations and the lines they formalize', '',
           'Generated by `sources.py` from its `ROWS` table; do not edit by hand.',
           '`python3 formal/lean/sources.py` (also run by `tests/test_lean_sources.py`) checks that',
           'every declaration is listed, every cited line still contains its quoted text, and every',
           'cited certificate value equals the literal in the Lean declaration.',
           f'Line numbers refer to this branch, based on `{COMMIT[:7]}`.', '',
           '| Lean | Claim | Doug\'s notes | Paper (pinned upstream) | Certificate / script | Remark |',
           '|---|---|---|---|---|---|']
    for module, names, claim, refs, remark in ROWS:
        lean = ', '.join(f'[`{n}`](KappaCheck/{module}.lean#L{decls[(module, n)][1]})'
                         for n in names)
        cols = {'notes': [], 'upstream': [], 'other': []}
        for ref in refs:
            top = ref.path.split('/')[0]
            cols[top if top in cols else 'other'].append(link(ref))
        cell = lambda xs: '<br>'.join(dict.fromkeys(xs)) or '—'
        out.append(f'| {lean} | {claim} | {cell(cols["notes"])} | {cell(cols["upstream"])} '
                   f'| {cell(cols["other"])} | {remark} |')
    return '\n'.join(out)+'\n'


if __name__ == '__main__':
    errs = check()
    target = LEAN/'SOURCES.md'
    if '--write' in sys.argv and not errs:
        target.write_text(render())
    elif not errs and target.read_text() != render():
        errs.append('SOURCES.md is stale: run sources.py --write')
    print('\n'.join(errs) or f'OK: {sum(len(r[1]) for r in ROWS)} declarations, '
          f'{sum(len(r[3]) for r in ROWS)} source references')
    sys.exit(1 if errs else 0)
