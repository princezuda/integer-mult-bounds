#!/usr/bin/env python3
"""Drift test: every Lean literal in PRChecksC equals the value in the PR's own JSON.

Modelled on main's `formal/lean/sources.py` (`Key` refs). For each PR worktree
(vendored under `data/pr9` .. `data/pr12`) it checks

* explicit `Key` rows: the certificate value at `keys` equals the Lean literal `lean`,
  and that literal occurs as a whole token in the named Lean declaration with its comments
  removed;
* automatic rows for the assembly: every JSON constraint / margin / recurrence key is
  stated in the Lean `slack_values` / `margin_values` / `recurrence_values` theorem
  with an equal literal (and no extra or missing names), and every JSON parameter equals
  the corresponding field of the Lean `def P : Params`;
* a few cross-PR text checks (PR #11's quoted κ against PR #10's JSON);
* a literal sweep: every integer literal of four or more digits (other than powers of ten)
  in the Lean modules, comments removed, is a digit string of some checked literal or is
  listed in `ALLOW` with the reason it is not PR data.

Run: python3 drift.py   (exit 1 on any mismatch)
"""
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import json
import re
import sys

HERE = Path(__file__).resolve().parent
PRS = HERE / 'data'
LEAN = HERE.parent / 'lean' / 'PRChecksC'


@dataclass(frozen=True)
class Key:
    pr: str          # worktree name, e.g. 'pr10'
    path: str        # JSON path inside the worktree
    keys: tuple      # path inside the JSON
    module: str      # Lean file stem
    decl: str        # Lean declaration name
    lean: str        # Lean literal as written


DECL = re.compile(r'^(?:noncomputable )?(?:theorem|def) (\S+)', re.M)
STOP = re.compile(r'^(?:theorem|def|noncomputable|/-|end |namespace|section)', re.M)


def strip_comments(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)


def lean_decls():
    """(module, name) -> declaration text with comments removed"""
    out = {}
    for f in sorted(LEAN.glob('*.lean')):
        text = f.read_text()
        for match in DECL.finditer(text):
            rest = text[match.end():]
            stop = STOP.search(rest)
            body = match.group(0) + (rest[:stop.start()] if stop else rest)
            out[(f.stem, match.group(1))] = strip_comments(body)
    return out


def norm(s):
    return ' '.join(s.split())


def has_token(body, literal):
    """`literal` occurs in `body` (whitespace-normalized), not inside a longer token"""
    return re.search(r'(?<![\w.])' + re.escape(norm(literal)) + r'(?![\w.])', norm(body)) is not None


def _eval(literal):
    """exact value of a Lean literal such as `761 / 10 ^ 11`, `1 / 21952` or `28 ^ 3`"""
    if not re.fullmatch(r'[0-9 /^]+', literal) or literal.count('/') > 1:
        raise ValueError(literal)
    num, _, den = literal.partition('/')
    ev = lambda t: eval(t.replace('^', '**'), {'__builtins__': {}}) if t.strip() else 1
    return Fraction(ev(num)) / Fraction(ev(den))


def json_at(pr, path, keys):
    x = json.loads((PRS / pr / path).read_text())
    for k in keys:
        x = x[k]
    return x


# ---------------------------------------------------------------------------
# Explicit rows
# ---------------------------------------------------------------------------
P9 = 'research/prime-field-followup/certificate.json'
P9V = 'research/prime-field-followup/vendor/prime-field28.json'
B10 = 'certificates/batched-network.json'
C10 = 'certificates/controlled-bit-rank-moment.json'
R11 = 'research/geometric-dimensions/report.json'
C12 = 'research/batched-followup/certificate.json'

ROWS = []


def rows(pr, path, prefix, module, table):
    for keys, decl, lean in table:
        ROWS.append(Key(pr, path, tuple(prefix) + tuple(keys), module, decl, lean))


# ---- PR #9 -------------------------------------------------------------------
rows('pr9', P9, ['witness', 'bit'], 'PR9', [
    (['v'], 'bit_counts', '98280'), (['m'], 'bit_counts', '21952'),
    (['N'], 'bit_counts', '949282431552000'), (['W'], 'bit_counts', '227349085594176000'),
    (['L'], 'bit_counts', '284784729465600'), (['D'], 'bit_counts', '379712972620800'),
    (['s'], 'bit_counts', '4990766747250378931200'), (['roles'], 'roles', '11670540'),
    (['eta'], 'bit_eta', '117 / 1537792480'), (['h'], 'm', '28')])
rows('pr9', P9, ['witness', 'retained_complex'], 'PR9', [
    (['v'], 'complex_counts', '3276'), (['N'], 'complex_counts', '35158608576'),
    (['I'], 'complex_counts', '32196528'), (['W'], 'complex_counts', '2085111546336'),
    (['L'], 'complex_counts', '26143580736'), (['D'], 'complex_counts', '18030055680'),
    (['s'], 'complex_counts', '45772350635112192'),
    (['scalar_gates'], 'complex_counts', '8702721518400'),
    (['roles'], 'Rc', '93838'), (['eta'], 'complex_eta', '5 / 12693352'),
    (['m'], 'm', '28 ^ 3')])
rows('pr9', P9, ['witness'], 'PR9', [
    (['bit_saving'], 'bit_exponent', '761 / 10 ^ 11'),
    (['complex_saving'], 'complex_exponent', '39 / 10 ^ 9'),
    (['guard', 'E'], 'guard_constants', '580186831374453739191483276086074980416'),
    (['guard', 'B'], 'guard_constants', '580186831374453739191529048436710092608'),
    (['guard', 'C0'], 'C0', '1330227007428750171975003167066483053874539349448633868671027791264533942584236249186304'),
    (['guard', 'C1'], 'guard_constants', '19601 / 10000'),
    (['guard', 'beta'], 'guard_constants', '19 / 25'),
    (['guard', 'zeta'], 'ζq', '1 / 10000'),
    (['minimum_margin'], 'margin_values', '4754049 / 1250000000000000'),
    (['absorption_gap'], 'kappa_witness', '4049 / 1250000000000000'),
    (['headline_ratio_to_pr7'], 'kappa_witness', '380 / 373')])
rows('pr9', P9, [], 'PR9', [
    (['independent_cpp_check', 'optimized_additions'], 'c_add', '10687362'),
    (['independent_cpp_check', 'role_upper_bound'], 'roles', '11670540'),
    (['independent_cpp_check', 'new_star_additions'], 'roles', '2452660'),
    (['selected_templates', 'saved_additions'], 'roles', '170400'),
    (['selected_templates', 'published_star_additions'], 'roles', '2623060'),
    (['global_before_replacement', 'outputs'], 'q_out', '983178')])
rows('pr9', P9V, [], 'PR9', [
    (['producer', 'independent_template_check', 'optimized_additions'], 'roles', '10857762'),
    (['producer', 'independent_template_check', 'role_upper_bound'], 'roles', '11840940'),
    (['witness', 'complex', 'roles'], 'Rc', '93838'),
    (['complex_checks', 'stats', 'additions'], 'additions_c', '61022'),
    (['witness', 'parameters', 'kappa'], 'kappa_witness', '373 / 10 ^ 11')])

# ---- PR #10 ------------------------------------------------------------------
BIT10 = [
    (['counts', 'v'], 'bit_counts', '98280'), (['counts', 'm'], 'bit_counts', '21952'),
    (['counts', 'N'], 'bit_counts', '949282431552000'),
    (['counts', 'W'], 'bit_counts', '230640858616896000'),
    (['counts', 'decreasing_dimension'], 'bit_counts', '284784729465600'),
    (['counts', 'deficit'], 'bit_counts', '379712972620800'),
    (['counts', 'original_rank_sum'], 'bit_counts', '5063027748645128371200'),
    (['counts', 'roles_per_invocation'], 'R', '11840940'),
    (['counts', 'singleton_calls'], 'bit_singletons', '105555640096680883200'),
    (['counts', 'eta'], 'bit_eta', '39 / 520019360'),
    (['counts', 'bulk_classes', 0, 'copies'], 'bit_counts', '114371146876896000'),
    (['counts', 'bulk_classes', 1, 'copies'], 'bit_counts', '114371146876896000'),
    (['counts', 'bulk_classes', 2, 'copies'], 'bit_counts', '1898564863104000'),
    (['counts', 'bulk_classes', 0, 'original_rank'], 'bit_classes', '21896'),
    (['counts', 'bulk_classes', 1, 'original_rank'], 'bit_classes', '21168'),
    (['counts', 'bulk_classes', 2, 'original_rank'], 'bit_classes', '21141'),
    (['counts', 'bulk_classes', 0, 'singleton_pivots'], 'bit_classes', '56'),
    (['counts', 'bulk_classes', 2, 'singleton_pivots'], 'bit_classes', '811'),
    (['counts', 'bulk_classes', 0, 'chunk_digits'], 'bit_classes', '21840'),
    (['counts', 'bulk_classes', 1, 'chunk_digits'], 'bit_classes', '20384'),
    (['counts', 'bulk_classes', 2, 'chunk_digits'], 'bit_classes', '20330'),
    (['counts', 'bulk_classes', 1, 'additional_corner_chunk_digits'], 'bit_classes', '784'),
    (['counts', 'recursive_blocks', 3, 'chunk_digits'], 'bit_classes', '784'),
    (['normalized_widths', 0], 'bit_logs', '1 / 21952'),
    (['normalized_widths', 1], 'bit_weights', '195 / 196'),
    (['normalized_widths', 2], 'bit_weights', '13 / 14'),
    (['normalized_widths', 3], 'bit_weights', '10165 / 10976'),
    (['normalized_widths', 4], 'bit_weights', '1 / 28'),
    (['rank_mass_weights', 0], 'bit_weights', '10841531 / 520019360'),
    (['rank_mass_weights', 1], 'bit_weights', '12827685 / 26000968'),
    (['rank_mass_weights', 2], 'bit_weights', '855179 / 1857212'),
    (['rank_mass_weights', 3], 'bit_weights', '20865 / 2736944'),
    (['rank_mass_weights', 4], 'bit_weights', '65783 / 3714424'),
    (['logarithm_upper_bounds', 0], 'bit_logs', '9997 / 1000'),
    (['logarithm_upper_bounds', 1], 'bit_logs', '16 / 3125'),
    (['logarithm_upper_bounds', 2], 'bit_logs', '7411 / 100000'),
    (['logarithm_upper_bounds', 3], 'bit_logs', '48 / 625'),
    (['logarithm_upper_bounds', 4], 'bit_logs', '33323 / 10000'),
    (['moment_upper'], 'bit_moment_upper',
     '832316498477146912564441713716480470146509771830369384326171875 / '
     '832316498516766812983714413733509306294639695517209061296295401'),
    (['strict_gap'], 'bit_moment_upper',
     '39619900419272700017028836148129923686839676970123526 / '
     '832316498516766812983714413733509306294639695517209061296295401'),
    (['bit_saving'], 'bit_moment', '246 / 10 ^ 9'),
]
rows('pr10', B10, ['bit'], 'PR10', BIT10)
rows('pr10', C10, [], 'PR10', BIT10)   # the standalone bit certificate is the same object

CPX10 = [
    (['counts', 'v'], 'complex_counts', '3276'), (['counts', 'm'], 'bit_counts', '21952'),
    (['counts', 'N'], 'complex_counts', '35158608576'),
    (['counts', 'W'], 'complex_counts', '2085111546336'),
    (['counts', 'L'], 'complex_counts', '26143580736'),
    (['counts', 'deficit'], 'complex_counts', '18030055680'),
    (['counts', 's'], 'complex_counts', '45772350635112192'),
    (['counts', 'side_roles'], 'Rc', '93838'),
    (['counts', 'auxiliary_roles'], 'complex_counts', '93867'),
    (['counts', 'singleton_calls'], 'complex_counts', '2389799139122304'),
    (['counts', 'bulk_classes', 0, 'copies'], 'complex_counts', '1007397164592'),
    (['counts', 'bulk_classes', 1, 'copies'], 'complex_counts', '1007397164592'),
    (['counts', 'bulk_classes', 0, 'rank'], 'complex_counts', '21896'),
    (['counts', 'bulk_classes', 1, 'rank'], 'complex_counts', '21168'),
    (['counts', 'eta'], 'complex_weights', '5 / 12693352'),
    (['normalized_widths', 0], 'complex_logs', '1 / 21952'),
    (['normalized_widths', 1], 'complex_weights', '391 / 392'),
    (['normalized_widths', 2], 'complex_weights', '27 / 28'),
    (['rank_mass_weights', 0], 'complex_weights', '1325453 / 25386704'),
    (['rank_mass_weights', 1], 'complex_weights', '12233999 / 25386704'),
    (['rank_mass_weights', 2], 'complex_weights', '844803 / 1813336'),
    (['logarithm_upper_bounds', 0], 'complex_logs', '9997 / 1000'),
    (['logarithm_upper_bounds', 1], 'complex_logs', '2555 / 10 ^ 6'),
    (['logarithm_upper_bounds', 2], 'complex_logs', '36368 / 10 ^ 6'),
    (['moment_upper'], 'complex_moment_upper',
     '1525632527231324124285650786113750000000 / 1525632551364197359955324563293421369131'),
    (['strict_gap'], 'complex_moment_upper',
     '24132873235669673777179671369131 / 1525632551364197359955324563293421369131'),
    (['complex_saving'], 'complex_moment', '7 / 10 ^ 7'),
]
GUARD10 = [
    (['C0'], 'C0', '16304044734034229354982033946533362986146411372544000'),
    (['C1'], 'guard_constants', '11999 / 10000'),
    (['E'], 'guard_constants', '580186831374453739191483276086074980416'),
    (['dependency_constant'], 'guard_constants', '580186831374453739191483276086075331649000'),
    (['m_to_rho_lower'], 'mlow', '160000'),
    (['q'], 'guard_constants', '22120'),
    (['h'], 'h', '28'), (['m'], 'bit_counts', '21952'),
    (['selected_ranks', 0], 'complex_counts', '21896'),
    (['selected_ranks', 1], 'complex_counts', '21168'),
    (['path_moment_upper', 'no_bulk'], 'path_moment_rational', '553 / 4000'),
    (['path_moment_upper', 'rank_21896'], 'path_moment_rational', '47817969 / 47897500'),
    (['path_moment_upper', 'rank_21168'], 'path_moment_rational', '1213697 / 1260000'),
    (['theta_upper'], 'θbar', '999 / 1000'),
    (['theta_slack'], 'path_moment_rational', '63267 / 95795000'),
    (['rho'], 'ρq', '6 / 5'), (['beta'], 'βq', '1 / 1000'), (['zeta'], 'ζq', '1 / 10000'),
]
rows('pr10', B10, ['complex'], 'PR10', CPX10)
rows('pr10', B10, ['assembly', 'guard'], 'PR10', GUARD10)
rows('pr10', B10, ['assembly'], 'PR10', [
    (['minimum_margin'], 'margin_values', '9839998762000001 / 80000000000000000000000'),
    (['absorption_gap'], 'kappa_witness', '362000001 / 80000000000000000000000'),
    (['dyadic_gap'], 'kappa_witness', '194083351 / 51200000000000000')])

# ---- PR #11 ------------------------------------------------------------------
for i, (h, R, eta) in enumerate([(24, '4728452', '253 / 5496141312'),
                                 (26, '7602157', '365 / 5183525412'),
                                 (27, '9476476', '260 / 3483601587'),
                                 (29, '14398188', '3 / 40094414'),
                                 (30, '17515487', '3857 / 52973979000'),
                                 (32, '25224960', '3503 / 52073136128')]):
    rows('pr11', R11, ['dimensions', i], 'PR11', [
        (['roles'], f'R{h}', R), (['eta'], 'screen_eta', eta), (['h'], 'screen_eta', f'DD {h}')])
rows('pr11', R11, ['family'], 'PR11', [(['target_bit_saving'], 'screens_reject', '761 / 10 ^ 11')])

# ---- PR #12 ------------------------------------------------------------------
rows('pr12', C12, ['bit'], 'PR12', [
    (['counts', 'v'], 'bit_counts', '142506'), (['counts', 'm'], 'bit_counts', '27000'),
    (['counts', 'h'], 'h', '30'),
    (['counts', 'N'], 'bit_counts', '2894006152890216'),
    (['counts', 'W'], 'bit_counts', '717195632319935496'),
    (['counts', 'decreasing_dimension'], 'bit_counts', '742052859715440'),
    (['counts', 'deficit'], 'bit_counts', '1409900433459336'),
    (['counts', 'original_rank_sum'], 'bit_counts', '19364280662737824932664'),
    (['counts', 'roles_per_invocation'], 'bit_counts', '17515487'),
    (['counts', 'singleton_calls'], 'bit_classes', '373570603170925665960'),
    (['counts', 'eta'], 'bit_eta', '3857 / 52973979000'),
    (['counts', 'bulk_classes', 0, 'copies'], 'bit_counts', '355703810007077532'),
    (['counts', 'bulk_classes', 1, 'copies'], 'bit_counts', '355703810007077532'),
    (['counts', 'bulk_classes', 2, 'copies'], 'bit_counts', '5788012305780432'),
    (['counts', 'bulk_classes', 0, 'original_rank'], 'bit_classes', '26940'),
    (['counts', 'bulk_classes', 1, 'original_rank'], 'bit_classes', '26100'),
    (['counts', 'bulk_classes', 2, 'original_rank'], 'bit_classes', '26071'),
    (['counts', 'bulk_classes', 0, 'singleton_pivots'], 'bit_classes', '60'),
    (['counts', 'bulk_classes', 2, 'singleton_pivots'], 'bit_classes', '929'),
    (['counts', 'bulk_classes', 0, 'chunk_digits'], 'bit_classes', '26880'),
    (['counts', 'bulk_classes', 1, 'chunk_digits'], 'bit_classes', '25200'),
    (['counts', 'bulk_classes', 2, 'chunk_digits'], 'bit_classes', '25142'),
    (['counts', 'bulk_classes', 1, 'additional_corner_chunk_digits'], 'bit_classes', '900'),
    (['counts', 'recursive_blocks', 3, 'chunk_digits'], 'bit_classes', '900'),
    (['ratios', 0], 'bit_logs', '1 / 27000'),
    (['ratios', 1], 'bit_weights', '224 / 225'),
    (['ratios', 2], 'bit_weights', '14 / 15'),
    (['ratios', 3], 'bit_weights', '12571 / 13500'),
    (['ratios', 4], 'bit_weights', '1 / 30'),
    (['weights', 0], 'bit_weights', '613175987 / 31784387400'),
    (['weights', 1], 'bit_weights', '1961734544 / 3973048425'),
    (['weights', 2], 'bit_weights', '122608409 / 264869895'),
    (['weights', 3], 'bit_weights', '33174869 / 4414498250'),
    (['weights', 4], 'bit_weights', '17515487 / 1059479580'),
    (['log_upper_bounds', 0], 'bit_logs', '2040718429 / 200000000'),
    (['log_upper_bounds', 1], 'bit_logs', '4454351 / 1000000000'),
    (['log_upper_bounds', 2], 'bit_logs', '8624109 / 125000000'),
    (['log_upper_bounds', 3], 'bit_logs', '8912139 / 125000000'),
    (['log_upper_bounds', 4], 'bit_logs', '1700598691 / 500000000'),
    (['moment_upper'], 'bit_moment_upper',
     '951397175334835659786955529971356627333020221426690409795882007543066085393917500000000000000 / '
     '951397175343791337554697540817110713134256690198498127782083171487866834310970992296187410241'),
    (['strict_gap'], 'bit_moment_upper',
     '8955677767742010845754085801236468771807717986201163944800748917053492296187410241 / '
     '951397175343791337554697540817110713134256690198498127782083171487866834310970992296187410241'),
    (['bit_saving'], 'bit_moment', '253 / 10 ^ 9')])
rows('pr12', C12, ['producer', 'checked'], 'PR12', [
    (['optimized_additions'], 'c_add', '16089992'),
    (['role_upper_bound'], 'bit_counts', '17515487'),
    (['optimized_stars'], 'proof_tex_numbers', '27405')])
rows('pr12', C12, ['producer', 'original'], 'PR12', [(['outputs'], 'Q_out', '1425495')])
rows('pr12', C12, ['complex'], 'PR10', CPX10)          # unchanged PR #10 complex network
rows('pr12', C12, ['assembly', 'guard'], 'PR10', GUARD10)
rows('pr12', C12, ['assembly'], 'PR12', [
    (['minimum_margin'], 'margin_values', '63249991095000007 / 500000000000000000000000'),
    (['absorption_gap'], 'kappa_witness', '4991095000007 / 500000000000000000000000')])
rows('pr12', C12, [], 'PR12', [(['kappa_ratio_to_pr10'], 'kappa_witness', '6324500 / 6149999')])

# Integer literals (>= 4 digits) of the Lean modules that are not certificate values.
ALLOW = {
    'Common': {
        '69314718055994530': 'our log 2 enclosure', '69314718055994531': 'our log 2 enclosure',
        '109861228866810969': 'our log 3 enclosure', '109861228866810970': 'our log 3 enclosure',
        '160943791243410037': 'our log 5 enclosure', '160943791243410038': 'our log 5 enclosure',
        '99966136': 'our bound log 21952 < 9.9966136', '33322046': 'our bound log 28 < 3.3322046',
        '340119738166215539': 'our bound on log 30',
        '1020359214498646617': 'our bound on log 27000',
    },
    'PR9': {
        '99966136': 'our bound log 21952 < 9.9966136 (the PR uses its own enclosure)',
        '20475': 'C(28,4), the star count', '7608': "README: lambda' = 1 - 7608/10^12",
        '38032392': 'g3 = 3.8032392e-9 in decimal, equal to the checked minimum margin',
    },
    'PR10': {
        '200000': '2555/10^6 = 511/200000 (complex_moment_upper)',
        '2273': '36368/10^6 = 2273/62500 (complex_moment_upper)', '62500': 'same',
        '195222619248167347200': 'S0 of the intermediate 177/10^9 certificate (not vendored)',
        '20051151': 'S0 weight numerator of the 177/10^9 certificate',
        '9018851588112489028174294032233536762346739': 'gap of the 177/10^9 certificate',
        '50604920044758147283008773507127786190942259516252989': 'same',
        '6993': 'batched-assembly.tex:95, leaf = 1 - 6993/10^10',
        '12299998': 'batched-assembly.tex:150, kappa = 1.2299998e-7',
        '32000000': 'patch exponent (1 - eps)/2 = 8000001/32000000',
        '95991988001': 'patch exponent eps*C1 = 95991988001/160000000000',
    },
    'PR11': {
        '13824': 'm = 24^3', '17576': 'm = 26^3', '19683': 'm = 27^3', '24389': 'm = 29^3',
        '32768': 'm = 32^3', '8000': '20^3 (q >= 7 tail)',
        '9534': 'our bound log 13824 >= 9.534', '98875': 'our bound log 19683 >= 9.8875',
        '102035': 'our bound log 27000 >= 10.2035',
        '1716': 'C(13,6)', '1717': '1 + C(13,6)',
        '282439008': 'q = 5 exact eta at h = 24, evaluated by q5_rows',
        '2553843750': 'same, h = 25', '1858802608': 'same, h = 26', '2323': 'same, h = 27',
        '47877204762': 'same, h = 27', '2810316992': 'same, h = 28', '15611447678': 'same, h = 29',
    },
    'PR12': {
        '102837': 'README "2.84% larger" bracket', '102838': 'same',
        '23000': 'proof.tex: C(5,2) C(25,3)',
        '599949916007': 'patch exponent eps*C1 = 599949916007/10^12',
    },
}

# ---------------------------------------------------------------------------
# Automatic assembly rows
# ---------------------------------------------------------------------------
ASSEMBLY = [('pr9', P9, ['witness'], 'PR9'), ('pr10', B10, ['assembly'], 'PR10'),
            ('pr12', C12, ['assembly'], 'PR12')]
FIELDS = {'τ': 'tau', 'σ': 'sigma', 'ε': 'epsilon', 'c': 'c', 'lam': 'lam', 'lamp': 'lamp',
          'κ': 'kappa', 'β': 'beta', 'δ': 'delta', 'C1': 'C1'}
PAIR = re.compile(r'P\.(\w+) = ([0-9 /^]+?)\s*(?:∧|$)')


def stated_pairs(body):
    body = body.split(':= by')[0]
    return {name: lit.strip() for name, lit in PAIR.findall(norm(body))}


def check_assembly(decls, errors):
    count = 0
    for pr, path, prefix, module in ASSEMBLY:
        x = json_at(pr, path, prefix)
        for theorem, jkey in (('slack_values', 'constraints'), ('margin_values', 'margins'),
                              ('recurrence_values', 'recurrence')):
            stated = stated_pairs(decls[(module, theorem)])
            expected = x[jkey]
            if set(stated) != set(expected):
                errors.append(f'{pr} {jkey}: Lean {theorem} names {sorted(set(stated) ^ set(expected))} differ')
            for k, v in expected.items():
                if k in stated:
                    count += 1
                    if _eval(stated[k]) != Fraction(str(v)):
                        errors.append(f'{pr} {path} {jkey}.{k}: {v} != Lean {stated[k]}')
        body = decls[(module, 'P')]
        fields = dict(re.findall(r'^\s*(\S+) := ([0-9 /^]+)$', body, re.M))
        if set(fields) != set(FIELDS):
            errors.append(f'{pr}: Lean P fields {sorted(fields)}')
        for f, k in FIELDS.items():
            count += 1
            if f in fields and _eval(fields[f]) != Fraction(str(x['parameters'][k])):
                errors.append(f'{pr} {path} parameters.{k}: {x["parameters"][k]} != Lean P.{f} {fields[f]}')
    return count


def check_text(errors):
    """PR #11 quotes PR #10's κ; PR #12 quotes PR #10's κ and its own."""
    k10 = Fraction(json_at('pr10', B10, ['assembly', 'parameters', 'kappa']))
    readme11 = (PRS / 'pr11/research/geometric-dimensions/README.md').read_text()
    m = re.search(r'kappa = (\d+)/(\d+)', readme11)
    if not m or Fraction(int(m.group(1)), int(m.group(2))) != k10:
        errors.append(f'pr11 README quotes {m and m.group(0)} but PR #10 JSON kappa is {k10}')
    k9 = Fraction(json_at('pr9', P9, ['witness', 'parameters', 'kappa']))
    if 'kappa = 3.8e-9' not in readme11 or k9 != Fraction(38, 10**10):
        errors.append('pr11 README PR #9 kappa quote')
    q5 = json_at('pr11', R11, ['family', 'q5', 'finite_dimensions'])
    zero = [r['h'] for r in q5 if r['upper'] == '0']
    if zero != list(range(15, 24)):
        errors.append(f'pr11 q5 zero rows {zero} != 15..23 (Lean q5_nonpositive)')
    return 3


def check():
    errors = []
    decls = lean_decls()
    for r in ROWS:
        try:
            value = Fraction(str(json_at(r.pr, r.path, r.keys)))
        except (KeyError, IndexError) as e:
            errors.append(f'{r.pr} {r.path} {r.keys}: missing ({e})')
            continue
        if (r.module, r.decl) not in decls:
            errors.append(f'{r.module}.{r.decl}: not found')
            continue
        body = decls[(r.module, r.decl)]
        literal = r.lean
        if literal.startswith('DD '):          # PR #11 dimension label
            if value != int(literal[3:]) or norm(literal) not in norm(body):
                errors.append(f'{r.pr} {r.keys}: dimension {value} vs {literal}')
            continue
        if _eval(literal) != value:
            errors.append(f'{r.pr} {r.path} {".".join(map(str, r.keys))}: {value} != Lean {literal}')
        elif not has_token(body, literal):
            errors.append(f'{r.module}.{r.decl}: literal {literal} not in declaration')
    n = len(ROWS) + check_assembly(decls, errors) + check_text(errors)
    n += sweep(decls, errors)
    return errors, n


def sweep(decls, errors):
    """every 4+ digit integer literal of the Lean modules is checked or explained"""
    accounted = set()
    for r in ROWS:
        accounted.update(re.findall(r'\d+', r.lean))
    for pr, path, prefix, module in ASSEMBLY:
        for theorem in ('slack_values', 'margin_values', 'recurrence_values', 'P'):
            accounted.update(re.findall(r'\d+', decls[(module, theorem)]))
    count = 0
    for f in sorted(LEAN.glob('*.lean')):
        text = strip_comments(f.read_text())
        for token in sorted(set(re.findall(r'(?<![\w.])\d{4,}(?![\w.])', text))):
            count += 1
            if re.fullmatch(r'10*', token) or token in accounted or token in ALLOW.get(f.stem, {}):
                continue
            errors.append(f'{f.name}: literal {token} is neither tied to the PR data nor allowed')
    return count


if __name__ == '__main__':
    errs, n = check()
    print('\n'.join(errs) or f'OK: {n} checks (certificate rows, assembly, text, literal sweep)')
    sys.exit(1 if errs else 0)
