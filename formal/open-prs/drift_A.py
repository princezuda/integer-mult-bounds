#!/usr/bin/env python3
"""Drift test for the Lean checks of PRs #3, #4 and #8 (pattern of main's `sources.py`).

Fails unless

1. every `Key` row's JSON value (in the PR's own certificate) equals the Lean literal, and
   that literal occurs in every named Lean declaration;
2. every `Line` row's note/doc lines still contain the quoted anchor, and its Lean literal
   occurs in every named declaration (numbers that exist only in the PR's prose);

   "occurs" means: as a whole token (not inside a longer number) in the declaration with its
   comments removed;
3. every entry of the certificates' `parameters`, `constraint_slacks`/`slacks`, `margins` and
   `recurrence`/`exponents` dicts appears in the Lean `P` / `slack_values` / `margin_values` /
   `recurrence_values` with an equal literal, and the Lean side has no extra entries;
4. every numeric leaf of each PR certificate is covered by (1)/(3), or listed in `EXCLUDED`
   with the reason it is not part of the Lean chain;
5. every integer literal of four or more digits (other than powers of ten) in the Lean PR
   modules is accounted for by (1)-(3) or listed in `ALLOW` with a reason, so no untracked
   number can enter the proofs;
6. `certificates/paired-network.json` (the retained bit network, used by `Bit.lean`) is
   byte-identical in the three worktrees.

Usage: python3 drift.py [--pr3 DIR] [--pr4 DIR] [--pr8 DIR]
"""
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / 'lean' / 'PRChecksA'
PRS = {'3': HERE / 'data' / 'pr3', '4': HERE / 'data' / 'pr4',
       '8': HERE / 'data' / 'pr8'}


@dataclass(frozen=True)
class Key:
    """Certificate value at `keys` of `path` (in PR `pr`) equals the Lean literal `lean`."""
    pr: str
    path: str
    keys: tuple
    lean: str


@dataclass(frozen=True)
class Line:
    """Lines `first..last` of `path` (in PR `pr`) contain `anchor`; `lean` is in the decl."""
    pr: str
    path: str
    first: int
    last: int
    anchor: str
    lean: str


PJ = 'certificates/paired-network.json'
C3 = 'certificates/complex-network.json'
N3 = 'notes/complex-circuit-note.tex'
K3 = 'notes/complex-circuit-construction.tex'
D3 = 'docs/research/complex-circuit.md'
C4 = 'certificates/retained-complex-layer.json'
D4 = 'docs/research/shared-retained-complex.md'
P4 = 'patches/retained-complex-31.patch'
K4 = 'notes/retained-complex-construction.tex'
R4 = 'README.md'
C8 = 'research/geometric-complex/certificate.json'
N8 = 'research/geometric-complex/geometric-note.tex'


def k3(*keys, lean):
    return Key('3', C3, keys, lean)


def w3(*keys, lean):
    return Key('3', C3, ('witness',)+keys, lean)


def k4(*keys, lean):
    return Key('4', C4, keys, lean)


def m4(*keys, lean):
    return Key('4', C4, ('main',)+keys, lean)


def k8(*keys, lean):
    return Key('8', C8, keys, lean)


def pj(*keys, lean):
    return Key('3', PJ, keys, lean)


# (module, declarations, refs)
ROWS = [
    # -- Bit.lean: the retained paired bit network (main's file, shared) -----------------
    ('Bit', ['R50'], [pj('bit_counts', 'side_roles_per_invocation', lean='509194')]),
    ('Bit', ['bit50_counts'], [
        pj('bit_counts', 'v', lean='19600'), pj('bit_counts', 'm', lean='125000'),
        pj('bit_counts', 'N', lean='7529536000000'), pj('bit_counts', 'W', lean='406321422080000'),
        pj('bit_counts', 'L', lean='2881200000000'), pj('bit_counts', 'D', lean='1767136000000'),
        pj('bit_counts', 's', lean='50790175992864000000')]),
    ('Bit', ['bit50_eta'], [pj('bit_counts', 'eta', lean='23 / 661055000')]),
    ('Bit', ['log_125000', 'bit50_exponent', 'tau_2964_certified'],
     [pj('log_m_upper', lean='11737 / 1000')]),
    ('Bit', ['bit50_exponent', 'ceiling_fixed_tau'], [pj('bit_saving', lean='296 / 10 ^ 11')]),
    ('Bit', ['ceiling_any_certified_tau'], [pj('bit_counts', 's', lean='50790175992864000000'),
                                            pj('bit_counts', 'W', lean='406321422080000')]),
    ('Bit', ['ceiling_fixed_tau'], [k3('scoped_ceiling', 'upper', lean='37 / 62500000000')]),
    ('Bit', ['beyond_fixed_tau_ceiling_3', 'beyond_fixed_tau_ceiling_8'],
     [k3('scoped_ceiling', 'upper', lean='37 / 62500000000')]),
    ('Bit', ['Pbeyond3', 'Pbeyond8'], [
        w3('parameters', 'epsilon', lean='19999 / 100000'),
        w3('parameters', 'beta', lean='1 / 1000'), w3('parameters', 'C1', lean='49961 / 10000')]),
    ('Bit', ['Pbeyond3'], [k3('complex_saving', lean='14 / 10 ^ 9')]),
    ('Bit', ['Pbeyond8'], [k8('complex_saving', lean='4 / 10 ^ 9')]),

    # -- PR3.lean -------------------------------------------------------------------------
    ('PR3', ['additions'], [k3('circuit', 'additions', lean='80595')]),
    ('PR3', ['disjoint_additions'], [k3('circuit', 'disjoint_additions', lean='68595')]),
    ('PR3', ['pair_star_additions'], [k3('circuit', 'pair_star_additions', lean='12000')]),
    ('PR3', ['injections'], [k3('circuit', 'injections', lean='27600')]),
    ('PR3', ['active_nodes'], [k3('labels', 'active_nodes', lean='82895')]),
    ('PR3', ['R'], [k3('circuit', 'roles', lean='108195'),
                    k3('complex_counts', 'side_roles_per_invocation', lean='108195'),
                    k3('role_frames', 'roles', lean='108195')]),
    ('PR3', ['circuit_bookkeeping'], [
        k3('complex_counts', 'original_side_wires_per_invocation', lean='3693800'),
        k3('side_map', 'nonzero_coefficients', lean='3693800')]),
    ('PR3', ['counts'], [
        k3('complex_counts', 'v', lean='2300'), k3('circuit', 'v', lean='2300'),
        k3('side_map', 'targets', lean='2300'),
        k3('complex_counts', 'm', lean='15625'), w3('guard', 'm', lean='15625'),
        k3('complex_counts', 'N', lean='12167000000'), k3('complex_counts', 'I', lean='15870000'),
        k3('complex_counts', 'W', lean='1741801270000'),
        k3('complex_counts', 'L', lean='10315500000'),
        k3('complex_counts', 's', lean='27215641140750000'),
        w3('guard', 's', lean='27215641140750000'),
        k3('complex_counts', 'deficit', lean='3703000000')]),
    ('PR3', ['W3', 'L3'], [k3('complex_counts', 'h', lean='25'), k3('circuit', 'h', lean='25')]),
    ('PR3', ['eta'], [k3('complex_counts', 'eta', lean='28 / 205789375')]),
    ('PR3', ['log_15625'], [k3('log_m_upper', lean='483 / 50')]),
    ('PR3', ['deficit_slack'], [
        k3('complex_deficit_slack', lean='6761797 / 8231575000000000'),
        k3('log_m_upper', lean='483 / 50'), k3('complex_saving', lean='7 / 500000000')]),
    ('PR3', ['exponent'], [k3('complex_saving', lean='7 / 500000000'),
                           k3('complex_counts', 'eta', lean='28 / 205789375')]),
    ('PR3', ['gate_bound'], [
        k3('gates', 'gates_per_invocation', lean='340784'),
        k3('gates', 'total_gates', lean='5408242080000'),
        k3('gates', 'twelve_W', lean='20901615240000')]),
    ('PR3', ['guard_constants'], [
        w3('guard', 'E', lean='338201706233372774319082463160146840064'),
        w3('guard', 'B', lean='338201706233372774319109678801287590064')]),
    ('PR3', ['C0'], [w3('guard', 'C0', lean='321727027889740762489223803495350305328695729120143793284991524019954162292886152000000')]),
    ('PR3', ['ζ'], [w3('guard', 'zeta', lean='1 / 10000')]),
    ('PR3', ['P'], [w3('guard', 'beta', lean='1 / 1000'), w3('guard', 'C1', lean='49961 / 10000')]),
    ('PR3', ['parameter_origin'], [
        k3('bit_saving', lean='37 / 12500000000'), k3('complex_saving', lean='7 / 500000000'),
        Line('3', N3, 50, 50, 'a=296/10^{11}', '296 / 10 ^ 11'),
        Line('3', N3, 50, 50, 'a_{\\rm c}=14/10^9', '14 / 10 ^ 9'),
        Line('3', N3, 56, 56, '\\lambda=1-\\frac{2958}{10^{12}}', '2958 / 10 ^ 12'),
        Line('3', N3, 57, 57, "\\lambda'=1-\\frac{2956}{10^{12}}", '2956 / 10 ^ 12'),
        Line('3', N3, 58, 58, '\\kappa=\\frac{59}{10^{11}}', '59 / 10 ^ 11')]),
    ('PR3', ['kappa_witness'], [
        w3('minimum_margin', lean='14779261 / 25000000000000000'),
        w3('absorption_gap', lean='29261 / 25000000000000000'),
        k3('improvement_over_compact_control', lean='590 / 83'),
        Line('3', N3, 89, 90, 'G_*=\\min_ig_i=g_3=\\frac{14779261}{25\\cdot10^{15}}', '14779261 / 25000000000000000'),
        Line('3', N3, 96, 96, '2^{-31}<\\frac{59}{10^{11}}<2^{-30}', '1 / 2 ^ 30')]),
    ('PR3', ['note_comparisons'], [
        Line('3', N3, 65, 65, '\\epsilon C_1=\\frac{999170039}{10^9}<1', '999170039 / 10 ^ 9'),
        Line('3', N3, 77, 77, 'p^{119999/400000}', '119999 / 400000'),
        Line('3', N3, 77, 77, 'p^{159997/200000}', '159997 / 200000'),
        Line('3', N3, 78, 78, '1-2\\epsilon=30001/50000>0', '30001 / 50000'),
        Line('3', K3, 218, 218, 'This is $33.49$ times the previous complex saving $418/10^{12}$', '3349'),
        Line('3', N3, 108, 108, 'by a factor $4.7$', '47')]),
    ('PR3', ['gaussian_cutoff'], [Line('3', N3, 77, 77, 'p^{159997/200000}', '159997')]),
    ('PR3', ['scoped_ceiling_values'], [
        k3('scoped_ceiling', 'upper', lean='37 / 62500000000'),
        k3('bit_saving', lean='37 / 12500000000'),
        Line('3', N3, 105, 105, '\\kappa<\\frac a5=\\frac{296}{5\\cdot10^{11}}<2^{-30}', '296 / (5 * 10 ^ 11)'),
        Line('3', N3, 107, 107, 'above $99.6\\%$ of this bound', '996')]),
    ('PR3', ['docs_line_102_is_equality'], [
        Line('3', D3, 102, 102, '`kappa < a_b/5 < 5.92e-10 < 2^-30`', '592 / 10 ^ 12')]),

    # -- PR4.lean -------------------------------------------------------------------------
    ('PR4', ['base_additions'], [m4('counts', 'base_additions', lean='66518')]),
    ('PR4', ['new_ancestors'], [m4('counts', 'new_ancestors', lean='120')]),
    ('PR4', ['side_outputs'], [m4('counts', 'side_outputs', lean='24288'),
                               k4('producer', 'partial_outputs', lean='24288')]),
    ('PR4', ['zero_output_uses'], [k4('producer', 'zero_output_uses', lean='12144')]),
    ('PR4', ['two_output_uses'], [k4('producer', 'two_output_uses', lean='12144')]),
    ('PR4', ['R'], [m4('counts', 'roles', lean='90950'), k4('producer', 'roles', lean='90950'),
                    k4('frames', 'roles', lean='90950')]),
    ('PR4', ['circuit_bookkeeping'], [
        m4('counts', 'additions', lean='66638'), k4('producer', 'additions', lean='66638'),
        m4('counts', 'retained_totals', lean='24'), k4('producer', 'retained_totals', lean='24'),
        Line('4', D4, 55, 55, 'C=66638, q=24312, R=90950', '24312')]),
    ('PR4', ['counts'], [
        m4('counts', 'v', lean='2024'), k4('producer', 'inputs', lean='2024'),
        m4('counts', 'm', lean='13824'), m4('counts', 'N', lean='8291469824'),
        m4('counts', 'W', lean='761750114048'), m4('counts', 'L', lean='6796219584'),
        m4('counts', 'D', lean='2990500480'), m4('counts', 's', lean='10530430586099072'),
        Line('4', P4, 1001, 1001, 'local loss $\\ell=(h-1)^2+h=553$', '553')]),
    ('PR4', ['W4', 'L4', 'D4', 's4', 'ell'], [m4('counts', 'h', lean='24'), k4('producer', 'h', lean='24')]),
    ('PR4', ['eta'], [m4('counts', 'eta', lean='365 / 1285272576')]),
    ('PR4', ['log_13824'], [m4('log_upper', lean='477 / 50')]),
    ('PR4', ['deficit_slack'], [
        m4('deficit_slack', lean='406952569 / 627574500000000000'),
        m4('log_upper', lean='477 / 50'), m4('constraint_slacks', 'sigma_below_one', lean='297 / 10000000000')]),
    ('PR4', ['exponent'], [m4('constraint_slacks', 'sigma_below_one', lean='297 / 10000000000'),
                           m4('counts', 'eta', lean='365 / 1285272576')]),
    ('PR4', ['gate_bound'], [m4('guard', 'scalar_gates', lean='3475338442752')]),
    ('PR4', ['guard_constants'], [
        m4('guard', 'E', lean='28288999069398280989721709640799207488'),
        m4('guard', 'B', lean='28288999069398280989732240071385306560')]),
    ('PR4', ['C0'], [m4('guard', 'C0', lean='1991520678995416584576942400432086873082564105960158546941478349741058754716840755200')]),
    ('PR4', ['ζ'], [m4('guard', 'zeta', lean='1 / 10000')]),
    ('PR4', ['P'], [m4('guard', 'C1', lean='49961 / 10000'), k4('kappa', lean='591 / 1000000000000')]),
    ('PR4', ['parameter_origin'], [
        Line('4', P4, 81, 81, 'a_{\\rm c}=2970/10^{11}', '2970 / 10 ^ 11'),
        Line('4', P4, 93, 93, '\\lambda=1-\\frac{2959}{10^{12}}', '2959 / 10 ^ 12'),
        Line('4', P4, 94, 94, "\\lambda'=1-\\frac{2958}{10^{12}}", '2958 / 10 ^ 12'),
        Line('4', P4, 95, 95, '\\kappa=\\frac{591}{10^{12}}>2^{-31}', '591 / 10 ^ 12')]),
    ('PR4', ['kappa_witness'], [
        m4('minimum_margin', lean='2956521 / 5000000000000000'),
        m4('absorption_gap', lean='1521 / 5000000000000000'),
        k4('ratio_over_compact_witness', lean='591 / 83')]),
    ('PR4', ['note_comparisons'], [
        Line('4', P4, 283, 283, '$\\alpha=\\Theta(p^{11999/40000})$', '11999 / 40000'),
        Line('4', P4, 284, 284, '$\\gamma=O(p^{15997/20000})=o(p)$', '15997 / 20000'),
        Line('4', P4, 285, 285, '$K=\\Theta(p^{1999/10000})=o(\\ell)$', '1999 / 10000'),
        Line('4', P4, 286, 286, '\\ell=\\Theta(p^{8001/10000})', '8001 / 10000'),
        Line('4', P4, 287, 287, '$p^{3001/5000}$', '3001 / 5000'),
        Line('4', R4, 40, 40, 'about **2.12 times**', '212'),
        Line('4', D4, 68, 68, 'about 2.12 times PR #3', '212'),
        Line('4', R4, 17, 17, '**591/83 ≈ 7.12 times**', '712'),
        Line('4', 'notes/compact-control-note.tex', 84, 84,
             '$\\epsilon C_1=99872039/10^8<1$', '99872039 / 10 ^ 8')]),
    ('PR4', ['gaussian_cutoff'], [Line('4', P4, 284, 284, 'p^{15997/20000}', '15997')]),
    ('PR4', ['rect_additions'], [Line('4', K4, 167, 167, 'gives $123855$ additions', '123855')]),
    ('PR4', ['rect_q0'], [Line('4', K4, 166, 166, '$q_0=205956$', '205956')]),
    ('PR4', ['rect_q2'], [Line('4', K4, 166, 166, '$q_2=27600$', '27600')]),
    ('PR4', ['rect_counts'], [
        Line('4', K4, 171, 171, 'or $8325$', '8325'),
        Line('4', K4, 172, 172, 'Thus $C=132180$', '132180'),
        Line('4', K4, 173, 173, '$q=q_0+q_2+h=233580$', '233580'),
        Line('4', K4, 173, 173, '$R_{\\rm aux}=365760$', '365760'),
        Line('4', K4, 176, 176, 'W=2N+2v^2R_{\\rm aux}=3013310215168', '3013310215168'),
        Line('4', K4, 180, 180, 's=Wm-2N+2L_{\\rm loss}=41655997423981952', '41655997423981952'),
        Line('4', K4, 181, 181, '\\eta=\\frac{Wm-s}{Wm}=\\frac{365}{5084246016}', '365 / 5084246016'),
        Line('4', K4, 194, 194, 'There are $6696869422848<12W$ scalar gates', '6696869422848')]),
    ('PR4', ['rect_slack'], [
        Line('4', K4, 190, 191, '=\\frac{11935523}{49650840000000000}>0', '11935523 / 49650840000000000'),
        Line('4', K4, 190, 190, '\\eta-\\frac{750}{10^{11}}\\frac{477}{50}', '750 / 10 ^ 11')]),
    ('PR4', ['rect_exponent'], [
        Line('4', K4, 186, 186, 'saving $1-\\sigma=750/10^{11}$', '750 / 10 ^ 11'),
        Line('4', 'notes/retained-complex-note.tex', 17, 17, '$1-\\sigma=750/10^{11}$', '750 / 10 ^ 11')]),

    # -- PR8.lean -------------------------------------------------------------------------
    ('PR8', ['disjoint_additions'], [k8('disjoint', 'additions', lean='212737'),
                                     k8('full_circuits', 0, 'additions', lean='212737')]),
    ('PR8', ['disjoint_outputs'], [k8('disjoint', 'outputs', lean='2300'),
                                   k8('full_circuits', 0, 'outputs', lean='2300')]),
    ('PR8', ['disjoint_roles'], [k8('disjoint', 'roles', lean='215037'),
                                 k8('full_circuits', 0, 'roles', lean='215037'),
                                 k8('full_circuits', 0, 'compiled_roles', lean='215037')]),
    ('PR8', ['two_additions'], [k8('intersection_two', 'additions', lean='36620'),
                                k8('full_circuits', 1, 'additions', lean='36620')]),
    ('PR8', ['two_outputs'], [k8('intersection_two', 'outputs', lean='6900'),
                              k8('full_circuits', 1, 'outputs', lean='6900')]),
    ('PR8', ['two_roles'], [k8('intersection_two', 'roles', lean='43520'),
                            k8('full_circuits', 1, 'roles', lean='43520'),
                            k8('full_circuits', 1, 'compiled_roles', lean='43520')]),
    ('PR8', ['circuit_bookkeeping'], [k8('side_roles', lean='258557'),
                                      k8('original_side_roles', lean='3693800')]),
    ('PR8', ['counts'], [
        k8('v', lean='2300'), k8('m', lean='17576'), k8('N', lean='12167000000'),
        k8('W', lean='4128046210000'), k8('L', lean='10728120000'),
        k8('s', lean='72554537309200000')]),
    ('PR8', ['W8', 'L8', 's8'], [k8('n', lean='25')]),
    ('PR8', ['L8', 's8'], [k8('h', lean='26')]),
    ('PR8', ['eta', 'saving_slack', 'exponent'], [k8('eta', lean='68 / 1714426753')]),
    ('PR8', ['saving_slack', 'exponent'], [k8('complex_saving', lean='1 / 250000000')]),
    ('PR8', ['guard_constants'], [
        k8('guard', 'scalar_depth_bound', lean='132486822720000'),
        k8('guard', 'E', lean='4502084376669118574298921305012335938112'),
        k8('guard', 'B', lean='4502084376669118574298993859549645138112')]),
    ('PR8', ['C0'], [k8('guard', 'C0', lean='64130294840276912774725352938289728105607858968597929848820159508267994713089753730056192')]),
    ('PR8', ['parameter_origin'], [
        Line('8', N8, 286, 286, '\\sigma=1-\\frac4{10^9}', '4 / 10 ^ 9'),
        Line('8', N8, 290, 290, '\\lambda=1-\\frac{2959}{10^{12}}', '2959 / 10 ^ 12'),
        Line('8', N8, 291, 291, "\\lambda'=1-\\frac{2958}{10^{12}}", '2958 / 10 ^ 12'),
        Line('8', N8, 292, 292, '\\kappa=\\frac{59}{10^{11}}', '59 / 10 ^ 11')]),
    ('PR8', ['kappa_witness'], [
        Key('8', C8, ('assembly', 'minimum_margin'), '2956521 / 5000000000000000'),
        k8('improvement_factor', lean='590 / 83'),
        Line('8', N8, 312, 312, '=5.913042\\cdot10^{-10}', '5913042 / 10 ^ 16'),
        Line('8', N8, 313, 313, 'G_*-\\kappa=1.3042\\cdot10^{-12}>0', '13042 / 10 ^ 16'),
        Line('8', N8, 334, 334, 'The saving ratio is $590/83\\simeq7.10843$', '710843')]),
    ('PR8', ['note_comparisons'], [
        Line('8', N8, 296, 296, 'is $1-3996/10^{12}$', '3996 / 10 ^ 12'),
        Line('8', N8, 301, 301, '$\\epsilon(1+c)=3998/10000<1$', '3998 / 10000'),
        Line('8', N8, 302, 302, '$\\epsilon C_1=99872039/10^8<1$', '99872039 / 10 ^ 8')]),
    ('PR8', ['gaussian_cutoff'], [
        Line('8', 'notes/compact-control-note.tex', 92, 92, '\\gamma=O(p^{15997/20000})=o(p)', '15997')]),
    ('PR8', ['scoped_ceiling_values'], [
        Line('8', N8, 337, 337, '$\\kappa<(296/10^{11})/5=5.92\\cdot10^{-10}$', '592 / 10 ^ 12'),
        Line('8', N8, 338, 338, 'over $99.6\\%$ of that ceiling', '996')]),
    ('PR8', ['phys6'], [k8('physical_phase_audit', 'invocations', i, 'physical_roles', lean='224')
                        for i in range(6)]),
    ('PR8', ['phys7'], [k8('physical_phase_audit', 'invocations', i, 'physical_roles', lean='554')
                        for i in range(6, 12)]),
    ('PR8', ['audit_small'],
     [k8('physical_phase_audit', 'invocations', i, field, lean=str(val))
      for i, val in enumerate([63450, 63450, 64890, 64890, 74970, 74970,
                               248426, 248426, 251856, 251856, 279296, 279296])
      for field in ('rank_sum', 'independently_derived_rank_sum')] +
     [k8('physical_phase_audit', 'invocations', i, 'decreasing_dimension', lean='49') for i in range(6)] +
     [k8('physical_phase_audit', 'invocations', i, 'decreasing_dimension', lean='64') for i in range(6, 12)]),
]

# The certificate dicts that are checked entry by entry: (pr, module, path, base keys, sections)
AUTO = [
    ('3', 'PR3', C3, ('witness',), {'parameters': 'P', 'constraint_slacks': 'slack_values',
                                     'margins': 'margin_values', 'recurrence': 'recurrence_values'}),
    ('4', 'PR4', C4, ('main',), {'parameters': 'P', 'constraint_slacks': 'slack_values',
                                 'margins': 'margin_values', 'exponents': 'recurrence_values'}),
    ('8', 'PR8', C8, ('assembly',), {'parameters': 'P', 'slacks': 'slack_values',
                                     'margins': 'margin_values', 'recurrence': 'recurrence_values'}),
]

# Numeric certificate leaves that are deliberately not formalized, with the reason.
EXCLUDED = {
    '3': {
        ('circuit', 'roles_per_target'): 'decimal display 47.041 of R/v; not in the chain',
        ('complex_counts', 'central_roles'): '= h + 1, written as `25 + 1` in W3/L3',
        ('labels', 'checked_inclusions'): 'count of finite label checks performed by the script',
        ('log_enclosure',): "the script's atanh enclosure of log 15625; Lean proves the bound "
                            'it supports, log 15625 < 483/50, directly (`log_15625`)',
    },
    '4': {
        ('main', 'log_interval'): "the script's atanh enclosure of log 13824; Lean proves "
                                  'log 13824 < 477/50 directly (`log_13824`)',
        ('producer', 'output_residual_checks'): 'count of finite residual checks performed',
    },
    '8': {
        ('complex_deficit_slack',): "eta - (4/10^9)*loghi with the script's atanh log enclosure; "
                                    'Lean uses log 17576 < 9775/1000 instead (`saving_slack`)',
        ('saving_lower',): "eta/loghi with the script's atanh enclosure; see above",
        ('full_circuits', 0, 'nested_role_incidences'): 'count of finite role checks',
        ('full_circuits', 1, 'nested_role_incidences'): 'count of finite role checks',
        ('physical_phase_audit', 'exhaustive_phase_addresses'): 'count of finite phase checks',
        ('physical_phase_audit', 'unique_binary_transitions'): 'count of finite checks',
        ('physical_phase_audit', 'invocations', '*', 'checked_incidences'): 'count of finite checks',
        ('physical_phase_audit', 'invocations', '*', 'n'): 'audit index (ground size 6 or 7)',
        ('physical_phase_audit', 'invocations', '*', 'stage'): 'audit index (stage 1-3)',
        ('small_audits',): 'counts of small exhaustive tests (n = 6, 7), not in the chain',
    },
}

# Integer literals (>= 4 digits) in the Lean PR modules that are not certificate values.
ALLOW = {
    'Bit': {
        '99703983': 'our q >= (15625/16384)^(1/16) for log 125000 < 11737/1000',
        '15625': '125000 = 2^17 * 15625/16384', '16384': '2^14',
        '117349': 'our lower bound log 125000 > 11.7349',
        '131072': '2^17', '125000': 'm_b, also bit_counts.m',
        '2964': 'negative control: re-certified 1 - tau = 2964/10^12',
        '2963': 'negative control lambda', '2962': 'negative control lambda prime',
        '5923': 'negative control kappa = 5923/10^13',
        '62500000000': 'denominator of scoped_ceiling.upper',
        '19999': 'PR #3 epsilon', '100000': 'PR #3 epsilon denominator',
        '49961': 'C1 numerator',
    },
    'PR3': {
        '99703983': 'our q >= (15625/16384)^(1/16) for log 15625 < 483/50',
        '15625': 'm = 25^3 = 2^14 * 15625/16384', '16384': '2^14',
        '3350': 'upper end of the 33.49 bracket',
        '125000': 'bit arity m_b in `witness_meets_general_ceiling` (tied in Bit.lean)', '1250000000000000': 'slack denominator',
        '62500000000': 'denominator of scoped_ceiling.upper',
    },
    'PR4': {
        '98943749': 'our q >= (27/32)^(1/16) for log 13824 < 477/50',
        '13824': 'm = 24^3 = 2^14 * 27/32', '2970': 'a_c = 2970/10^11 (patch line 81)',
        '62500000000': 'denominator of the fixed-tau ceiling 37/62500000000',
    },
    'PR8': {
        '100439897': 'our q >= (2197/2048)^(1/16) for log 17576 < 9775/1000',
        '2197': '17576 = 2^14 * 2197/2048', '2048': '2^11',
        '17576': 'm = 26^3', '9775': 'our rational log bound (the note states none)',
        '710844': 'upper end of the 7.10843 bracket',
        '15870000': 'I = 3v^2 at v = 2300, derived (the certificate does not record I)',
        '6521': 'G* - kappa = 6521/(5*10^15), the same value as 13042/10^16 (note line 313)',
        '62500000000': 'denominator of the fixed-tau ceiling 37/62500000000',
    },
}

DECL = re.compile(r'^(?:noncomputable )?(?:theorem|def) (\S+)', re.M)
STOP = re.compile(r'^(?:theorem|def|noncomputable|/-|end |namespace|section|macro|structure)', re.M)


def lean_decls():
    """(module, name) -> declaration text with comments removed"""
    out = {}
    for f in sorted(LEAN.glob('*.lean')):
        text = f.read_text()
        for match in DECL.finditer(text):
            rest = text[match.end():]
            stop = STOP.search(rest)
            body = match.group(0)+(rest[:stop.start()] if stop else rest)
            out[(f.stem, match.group(1))] = strip_comments(body)
    return out


def norm(s):
    return ' '.join(s.split())


def has_token(body, literal):
    """`literal` occurs in `body` (whitespace-normalized), not inside a longer token"""
    return re.search(r'(?<![\w.])' + re.escape(norm(literal)) + r'(?![\w.])', norm(body)) is not None


def lean_value(literal):
    """`a`, `a / b`, with `^`, `*` and parentheses allowed inside `a` and `b`."""
    if not re.fullmatch(r'[0-9 /^()*]+', literal):
        raise ValueError(literal)
    a, _, b = literal.partition('/')
    ev = lambda t: Fraction(eval(t.replace('^', '**'))) if t.strip() else Fraction(1)
    return ev(a)/ev(b)


def json_at(pr, path, keys):
    x = json.loads((PRS[pr]/path).read_text())
    for k in keys:
        x = x[k]
    return x


def to_fraction(x):
    return Fraction(str(x))


NUMERIC = re.compile(r'^-?\d+(?:\.\d+)?(?:/\d+)?$')


def numeric_leaves(x, path=()):
    if isinstance(x, bool):
        return
    if isinstance(x, dict):
        for k, y in x.items():
            yield from numeric_leaves(y, path+(k,))
    elif isinstance(x, list):
        for i, y in enumerate(x):
            yield from numeric_leaves(y, path+(i,))
    elif isinstance(x, int) or (isinstance(x, str) and NUMERIC.match(x)):
        yield path


def excluded(pr, path):
    for prefix in EXCLUDED.get(pr, {}):
        if len(prefix) <= len(path) and all(p == '*' or p == q for p, q in zip(prefix, path)):
            return True
    return False


def strip_comments(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)


def check():
    errors = []
    decls = lean_decls()
    covered = {pr: set() for pr in PRS}
    accounted = {}
    n_refs = 0
    for module, names, refs in ROWS:
        for name in names:
            if (module, name) not in decls:
                errors.append(f'{module}.{name}: not found in Lean sources')
        for ref in refs:
            n_refs += 1
            accounted.setdefault(module, set()).update(re.findall(r'\d+', ref.lean))
            for name in names:
                if not has_token(decls.get((module, name), ''), ref.lean):
                    errors.append(f'{module}.{name}: literal `{ref.lean}` not in declaration')
            if isinstance(ref, Line):
                lines = (PRS[ref.pr]/ref.path).read_text().split('\n')
                if not 1 <= ref.first <= ref.last <= len(lines):
                    errors.append(f'PR{ref.pr} {ref.path}:{ref.first}-{ref.last}: out of range')
                elif norm(ref.anchor) not in norm(' '.join(lines[ref.first-1:ref.last])):
                    errors.append(f'PR{ref.pr} {ref.path}:{ref.first}-{ref.last}: anchor {ref.anchor!r} missing')
            else:
                try:
                    value = to_fraction(json_at(ref.pr, ref.path, ref.keys))
                except (KeyError, IndexError):
                    errors.append(f'PR{ref.pr} {ref.path} {ref.keys}: missing key')
                    continue
                if ref.path != PJ:
                    covered[ref.pr].add(tuple(ref.keys))
                if lean_value(ref.lean) != value:
                    errors.append(f'PR{ref.pr} {ref.path} {".".join(map(str, ref.keys))}: '
                                  f'certificate {value} != Lean {ref.lean}')
    for pr, module, path, base, sections in AUTO:
        for section, decl in sections.items():
            data = json_at(pr, path, base+(section,))
            body = decls.get((module, decl), '')
            if decl == 'P':
                found = dict(re.findall(r'(?<![A-Za-z_.])([A-Za-z_0-9]+) := ([0-9 /]+?)\s*(?:,|\})', body))
            else:
                found = dict(re.findall(r'P\.([A-Za-z_0-9]+) = ([0-9 /]+?)\s*(?:∧|:=)', body))
            for key, val in data.items():
                n_refs += 1
                covered[pr].add(base+(section, key))
                if key not in found:
                    errors.append(f'PR{pr} {section}.{key}: missing from {module}.{decl}')
                    continue
                accounted.setdefault(module, set()).update(re.findall(r'\d+', found[key]))
                if lean_value(found[key]) != to_fraction(val):
                    errors.append(f'PR{pr} {section}.{key}: certificate {val} != Lean {found[key]}')
            for key in set(found)-set(data):
                errors.append(f'{module}.{decl}: `{key}` has no certificate entry in {section}')
    for pr, path in (('3', C3), ('4', C4), ('8', C8)):
        for leaf in numeric_leaves(json.loads((PRS[pr]/path).read_text())):
            if leaf not in covered[pr] and not excluded(pr, leaf):
                errors.append(f'PR{pr} {path} {".".join(map(str, leaf))}: numeric value neither '
                              'checked against Lean nor excluded')
    for module in ('Bit', 'PR3', 'PR4', 'PR8'):
        text = strip_comments((LEAN/f'{module}.lean').read_text())
        for token in sorted(set(re.findall(r'(?<![\w.])\d{4,}(?![\w.])', text))):
            if re.fullmatch(r'10*', token):
                continue
            if token not in accounted.get(module, set()) and token not in ALLOW.get(module, {}):
                errors.append(f'{module}.lean: literal {token} is neither tied to the PR data nor allowed')
    digests = {pr: hashlib.sha256((PRS[pr]/PJ).read_bytes()).hexdigest() for pr in PRS}
    if len(set(digests.values())) != 1:
        errors.append(f'{PJ} differs between the worktrees: {digests}')
    return errors, n_refs


if __name__ == '__main__':
    args = sys.argv[1:]
    for flag, pr in (('--pr3', '3'), ('--pr4', '4'), ('--pr8', '8')):
        if flag in args:
            PRS[pr] = Path(args[args.index(flag)+1])
    errs, n = check()
    print('\n'.join(errs) or f'OK: {n} certificate/note references checked against the Lean literals')
    sys.exit(1 if errs else 0)
