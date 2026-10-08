#!/usr/bin/env python3
"""Drift test: every annotated Lean literal equals the value in the PR's own certificate.

Each checked line of `PRChecksB/*.lean` ends with a tag

    <lean code ending in a literal>  -- json <certificate>.json <dotted.key.path>

(the `Key` refs of `formal/lean/sources.py`, written inline). The checked literal is the
last numeric literal `a` or `a / b` in the code part of the line. The certificate is read
from the worktree of the PR that the module checks (`MODULES`), at
`certificates/<certificate>.json`; list indices in paths are integers.

The checked literal may be `a`, `a / b`, `a / b ^ k` or `a ^ k`. Numbers that exist only in
the PR's notes and scripts (PR5Analytic) are `LINES` rows: the cited vendored lines contain
the anchor and the Lean literal occurs, as a token and outside comments, in the declaration.

The test fails if
  * a tagged literal differs from the certificate value (exact `Fraction` comparison),
    or a tagged path does not exist, or a tagged line has no literal;
  * a core certificate value (`REQUIRED` prefixes: counts, eta, log bounds, guard,
    parameters, slacks, recurrence, margins, minimum, gap, ceiling) has no tag;
  * a `LINES` anchor is missing from its lines, or its literal from its declaration;
  * an exponent certificate or deficit slack does not use its tagged saving (`USES`);
  * a definition whose body is a numeric expression, or a numeric `Params` field, has neither
    a tag nor a `LINES` row (lines marked `-- audit` are audit-chosen witnesses, not PR data);
  * PR #6's or #7's copy of `complex-network.json` / `fast-gaussian.json` differs from PR #5's;
  * a Lean file contains `sorry`, `admit`, `native_decide` or an `axiom` declaration.

Usage: python3 drift.py [--selftest] [PR5=/path/to/worktree ...]
`--selftest` also perturbs one certificate value per module in memory and checks that
the test then reports exactly that tag.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / 'lean' / 'PRChecksB'

# module -> PR worktree whose certificates it checks
MODULES = {
    'PR5': str(HERE / 'data' / 'pr5'),
    'PR5Analytic': str(HERE / 'data' / 'pr5'),
    'PR6': str(HERE / 'data' / 'pr6'),
    'PR7': str(HERE / 'data' / 'pr7'),
}

# (module, certificate) -> key prefixes whose numeric leaves must all be tagged
REQUIRED = {
    ('PR5', 'complex-network.json'): [
        'complex_counts.v', 'complex_counts.m', 'complex_counts.N', 'complex_counts.I',
        'complex_counts.W', 'complex_counts.L', 'complex_counts.s', 'complex_counts.deficit',
        'complex_counts.eta', 'complex_counts.side_roles_per_invocation',
        'complex_counts.original_side_wires_per_invocation', 'complex_deficit_slack',
        'complex_saving', 'bit_saving', 'log_m_upper', 'log_enclosure', 'gates',
        'scoped_ceiling.upper', 'improvement_over_compact_control', 'labels.active_nodes',
        'witness.guard', 'witness.parameters', 'witness.constraint_slacks', 'witness.recurrence',
        'witness.margins', 'witness.minimum_margin', 'witness.absorption_gap'],
    ('PR5', 'paired-network.json'): [
        'bit_counts', 'bit_saving', 'bit_deficit_slack', 'log_m_upper'],
    ('PR5', 'fast-gaussian.json'): [
        'complex_counts.W', 'complex_counts.s', 'complex_counts.eta', 'complex_saving',
        'bit_saving', 'scoped_ceiling.upper', 'improvement_over_compact_control',
        'improvement_over_compressed_complex', 'neumann_samples',
        'witness.guard', 'witness.parameters', 'witness.constraint_slacks', 'witness.recurrence',
        'witness.margins', 'witness.minimum_margin', 'witness.absorption_gap'],
    ('PR6', 'aligned-bit-network.json'): [
        'bit_counts.v', 'bit_counts.m', 'bit_counts.N', 'bit_counts.W', 'bit_counts.L',
        'bit_counts.s', 'bit_counts.deficit', 'bit_counts.eta', 'bit_counts.published_roles',
        'bit_counts.side_and_center_roles', 'bit_deficit_slack', 'bit_saving', 'complex_saving',
        'previous_bit_saving', 'previous_counts.deficit', 'log_m_upper', 'log_enclosure',
        'scoped_ceiling.upper', 'improvement_over_fast_gaussian',
        'witness.guard', 'witness.parameters', 'witness.constraint_slacks', 'witness.recurrence',
        'witness.margins', 'witness.minimum_margin', 'witness.absorption_gap'],
    ('PR7', 'prime-field28.json'): [
        'witness.bit.v', 'witness.bit.m', 'witness.bit.N', 'witness.bit.W', 'witness.bit.L',
        'witness.bit.D', 'witness.bit.s', 'witness.bit.eta', 'witness.bit.roles',
        'witness.bit.retained_totals', 'witness.complex.v', 'witness.complex.m',
        'witness.complex.N', 'witness.complex.I', 'witness.complex.W', 'witness.complex.L',
        'witness.complex.D', 'witness.complex.s', 'witness.complex.eta', 'witness.complex.roles',
        'witness.complex.scalar_gates', 'witness.deficit_slacks', 'witness.log_upper',
        'witness.guard', 'witness.parameters', 'witness.constraints', 'witness.recurrence',
        'witness.margins', 'witness.minimum_margin', 'witness.absorption_gap'],
}

TAG = re.compile(r'--\s*json\s+(\S+\.json)\s+(\S+)\s*$')
LIT = re.compile(r'(?<![\w.])(\d+)(?:\s*\^\s*(\d+))?(?:\s*/\s*(\d+)(?:\s*\^\s*(\d+))?)?(?![\w.])')
AUDIT = re.compile(r'--\s*audit\b')

# Copies that must be byte-identical to PR #5's (the branches are stacked on it).
SHARED = [('pr6', 'certificates/complex-network.json'), ('pr6', 'certificates/fast-gaussian.json'),
          ('pr7', 'certificates/complex-network.json'), ('pr7', 'certificates/fast-gaussian.json')]

FG = 'notes/fast-gaussian-resampling.tex'
FN = 'notes/fast-gaussian-note.tex'
FS = 'scripts/fast_gaussian.py'
# (module, declaration, vendored path, first, last, anchor, Lean literal)
LINES = [
    ('PR5Analytic', 'kappa0_bounds', FG, 77, 77, r'4.531<\kappa_0<4.534', '4531 / 1000'),
    ('PR5Analytic', 'kappa0_bounds', FG, 77, 77, r'4.531<\kappa_0<4.534', '4534 / 1000'),
    ('PR5Analytic', 'log_201', FG, 78, 78, r'\log_22.01<1.01', '101 / 100'),
    ('PR5Analytic', 'inner_sum_bound', FG, 56, 56, r'\pi\alpha^2\sigma>4\pi', '4 * π'),
    ('PR5Analytic', 'inner_sum_constant', FG, 57, 57, r'<2.01e^{-\pi\alpha^2\sigma}', '201 / 100'),
    ('PR5Analytic', 'neumann_log', FG, 76, 76, r'(p+1)/(4\alpha^2)+1/\theta',
     '(p + 1) / (4 * A) + 1 / θ'),
    ('PR5Analytic', 'neumann_power', FG, 20, 21, r'e^{\pi\alpha^2(1/(4\theta)+1/2)}',
     'π * A * (1 / (4 * θ) + 1 / 2)'),
    ('PR5Analytic', 'neumann_power', FG, 20, 21, r'2.01\,e^{-\pi\alpha^2\sigma}', '201 / 100'),
    ('PR5Analytic', 'lemma46_constant', FN, 87, 87, r'\|N-I\|<0.42', '42 / 100'),
    ('PR5Analytic', 'lemma46_dyadic', FN, 62, 62, r'2.01e^{-\pi\alpha^2\theta/2}<2^{-\alpha^2\theta}',
     '201 / 100'),
    ('PR5Analytic', 'neumann_norms', FN, 86, 86, r"\|\mathsf J'\|<7/8", '7 / 8'),
    ('PR5Analytic', 'sqrt_window', FG, 169, 170, r'(\pi/4)(1.21p)', '121 / 100 * p'),
    ('PR5Analytic', 'sqrt_window', FG, 170, 170, r'p>100', '100 ≤ p'),
    ('PR5Analytic', 'gamma_S_constant', FG, 169, 169, r'(\pi/4)(1.21p)', '121 / 100'),
    ('PR5Analytic', 'gamma_S_constant', FG, 170, 170, r'\Gamma=\lceil1.4p\rceil', '14 / 10'),
    ('PR5Analytic', 'F_constant', FG, 191, 191, r'2^{1.14\alpha^2}', '114 / 100'),
    ('PR5Analytic', 'window_E', FG, 198, 198, r'(\sqrt p+4\alpha)^2<25p', '25 * p'),
    ('PR5Analytic', 'gamma_E_constant', FG, 195, 195, r'\frac{25\pi}4p', '25 * π / 4'),
    ('PR5Analytic', 'gamma_E_constant', FG, 197, 197, r'\Gamma=\lceil29p\rceil', '29 * Real.log 2'),
    ('PR5Analytic', 'error_budgets', FG, 173, 173, r'(1+1/4+1)<3\cdot2^{-p}', '(1 : ℚ) + 1 / 4 + 1 < 3'),
    ('PR5Analytic', 'error_budgets', FG, 202, 202, r'(3+1+1)2^{-p}<(p/3)2^{-p}',
     '(3 + 1 + 1 : ℚ) < p / 3'),
    ('PR5Analytic', 'budget_S', FG, 171, 171, r'P=3p', '3 * p'),
    ('PR5Analytic', 'budget_S', FG, 170, 170, r'\Gamma=\lceil1.4p\rceil', '14 / 10 * p'),
    ('PR5Analytic', 'budget_E', FG, 197, 197, r'P=34p', '34 * p'),
    ('PR5Analytic', 'budget_E', FG, 197, 197, r'\Gamma=\lceil29p\rceil', '29 * p'),
    ('PR5Analytic', 'budget_E', FG, 191, 191, r'2^{1.14\alpha^2}', '114 / 100 * p'),
    ('PR5Analytic', 'gaussian_width', FN, 115, 115, r'b\ge96d', '96 * d'),
    ('PR5Analytic', 'gaussian_width', FN, 115, 115, r'\alpha^2\ge b/(16d)', 'b / (16 * d)'),
    ('PR5Analytic', 'gaussian_width', FN, 112, 112, r'\gamma=2d\alpha^2\le b/4',
     '2 * d * (α : ℝ) ^ 2 ≤ b / 4'),
    ('PR5Analytic', 'neumann_le_30d', FN, 121, 121, r'\le30d', '30 * d'),
    ('PR5Analytic', 'theta_window', FN, 117, 117, r'1/(2d-1)\le1/4', '1 / (2 * d - 1) ≤ 1 / 4'),
    ('PR5Analytic', 'alpha_theta', FN, 117, 117, r'b/(64d^2)\ge1', 'b / (64 * d ^ 2)'),
    ('PR5Analytic', 'alpha_theta', FN, 118, 118, r'b\ge64d^2', '64 * d ^ 2 ≤ b'),
    ('PR5Analytic', 'K0LO', FS, 34, 34, 'KAPPA0_LO = Q(333, 106)/Q(6932, 10000)',
     '(333 / 106) / (6932 / 10000)'),
    ('PR5Analytic', 'K0HI', FS, 35, 35, 'KAPPA0_HI = Q(355, 113)/Q(693, 1000)',
     '(355 / 113) / (693 / 1000)'),
    ('PR5Analytic', 'script_step', FS, 133, 133, 'Q(201, 100)**100 < 2**101',
     '((201 : ℚ) / 100) ^ 100 < 2 ^ 101'),
    ('PR5Analytic', 'script_step', FS, 134, 134, 'KAPPA0_LO*a2-Q(101, 100) >= 4*a2',
     '4 * A ≤ K0LO * A - 101 / 100'),
    ('PR5Analytic', 'SampleOK', FS, 146, 146, 'while 8*d*alpha**2 > b', '8 * d * α ^ 2 ≤ b'),
    ('PR5Analytic', 'SampleOK', FS, 149, 149, 'gamma*4 <= b', '4 * γ ≤ b'),
    ('PR5Analytic', 'SampleOK', FS, 160, 160, "x['n_new'] <= 30*x['d']", 'nNew ≤ 30 * d'),
    ('PR5Analytic', 'SampleOK', FS, 132, 132, 'theta < 1', '(1 : ℚ) / (4 * d) < 1'),
    ('PR5Analytic', 'SampleOK', FS, 135, 135, 'n_new = ceil(Q(p_bits+1, 4*a2)+1/theta)',
     '(6 * b + 1 : ℚ) / (4 * α ^ 2) + 4 * d ≤ nNew'),
    ('PR5Analytic', 'SampleOK', FS, 136, 136,
     '4*a2*n_new >= p_bits+1+KAPPA0_HI*a2*(1/(4*theta)+Q(1, 2))',
     'K0HI * α ^ 2 * (d + 1 / 2) ≤ 4 * α ^ 2 * nNew'),
    ('PR5Analytic', 'SampleOK', FS, 137, 137, 'n_hvdh = ceil(Q(p_bits)/(a2*theta))',
     '(6 * b : ℚ) * (4 * d) / α ^ 2 ≤ nH'),
]

# Declarations that must state their certified exponent through the tagged saving (and so
# cannot be weakened to a literal): (module, declaration, required text)
USES = [
    ('PR5', 'complex_exponent', '(15625 : ℝ) ^ (1 - (aC : ℝ))'),
    ('PR5', 'bit_exponent', '(125000 : ℝ) ^ (1 - (aB : ℝ))'),
    ('PR6', 'bit_exponent', '(125000 : ℝ) ^ (1 - (aB : ℝ))'),
    ('PR7', 'bit_exponent', '(21952 : ℝ) ^ (1 - (aB : ℝ))'),
    ('PR7', 'complex_exponent', '(21952 : ℝ) ^ (1 - (aC : ℝ))'),
    ('PR5', 'deficit_slack', 'aC * (966 / 100)'),
    ('PR5', 'bit_deficit_slack', 'aB * (11737 / 1000)'),
    ('PR6', 'deficit_slack', 'aB * (11737 / 1000)'),
    ('PR7', 'bit_deficit_slack', 'aB * (9997 / 1000)'),
    ('PR7', 'complex_deficit_slack', 'aC * 10'),
]

DECL = re.compile(r'^(?:noncomputable )?(?:theorem|def) (\S+)', re.M)
STOP = re.compile(r'^(?:theorem|def|noncomputable|/-|end |namespace|section|structure)', re.M)
NUMERIC = re.compile(r'^-?\d+(?:/\d+)?$')
FORBIDDEN = [(re.compile(r'\bsorry\b'), 'sorry'), (re.compile(r'\badmit\b'), 'admit'),
             (re.compile(r'native_decide'), 'native_decide'),
             (re.compile(r'^\s*(?:private\s+)?axiom\b', re.M), 'axiom declaration')]


def strip_comments(text):
    text = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)


def norm(s):
    return ' '.join(s.split())


def has_token(body, literal):
    """`literal` occurs in `body` (whitespace-normalized) and is not part of a longer token"""
    pat = r'(?<![\w.])' + re.escape(norm(literal)) + r'(?![\w.])'
    return re.search(pat, norm(body)) is not None


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


def lit_value(lit):
    m = LIT.fullmatch(lit.strip())
    a, e, b, f = (int(x) if x else None for x in m.groups())
    num = Fraction(a) ** (e or 1)
    den = Fraction(b) ** (f or 1) if b is not None else Fraction(1)
    return num / den


def at(data, path):
    for k in path.split('.'):
        data = data[int(k)] if isinstance(data, list) else data[k]
    return data


def leaves(data, prefix=''):
    if isinstance(data, dict):
        for k, v in data.items():
            yield from leaves(v, f'{prefix}.{k}' if prefix else k)
    elif isinstance(data, list):
        for i, v in enumerate(data):
            yield from leaves(v, f'{prefix}.{i}' if prefix else str(i))
    elif not isinstance(data, bool) and NUMERIC.match(str(data)):
        yield prefix, data


def tags():
    """Yield (module, file, line number, literal text, certificate, path)."""
    for f in sorted(LEAN.glob('*.lean')):
        for n, line in enumerate(f.read_text().split('\n'), 1):
            m = TAG.search(line)
            if not m:
                continue
            code = line[:line.index('--')]
            lits = list(LIT.finditer(code))
            yield f.stem, f, n, (lits[-1].group(0) if lits else None), m.group(1), m.group(2)


def check(roots, overrides=None):
    overrides = overrides or {}
    errors, cache, seen, count = [], {}, set(), 0
    for module, f, n, lit, cert, path in tags():
        where = f'{f.name}:{n}'
        if module not in roots:
            errors.append(f'{where}: module {module} has no PR worktree')
            continue
        root = roots[module]
        key = (root, cert)
        if key not in cache:
            try:
                cache[key] = json.loads((Path(root) / 'certificates' / cert).read_text())
            except FileNotFoundError:
                errors.append(f'{where}: {root}/certificates/{cert} not found')
                cache[key] = None
        if cache[key] is None:
            continue
        try:
            value = overrides.get((root, cert, path), at(cache[key], path))
        except (KeyError, IndexError, ValueError):
            errors.append(f'{where}: {cert} has no key {path}')
            continue
        if lit is None:
            errors.append(f'{where}: no literal before the tag for {cert} {path}')
            continue
        lean = lit_value(lit)
        want = Fraction(str(value))
        count += 1
        seen.add((root, cert, path))
        if lean != want:
            errors.append(f'{where}: Lean literal {lit} != {cert} {path} = {value}')
    for (module, cert), prefixes in REQUIRED.items():
        root = roots[module]
        data = cache.get((root, cert))
        if data is None:
            continue
        for prefix in prefixes:
            found = [p for p, _ in leaves(at(data, prefix), prefix)]
            if not found:
                errors.append(f'{cert}: required prefix {prefix} has no numeric value')
            for p in found:
                if (root, cert, p) not in seen:
                    errors.append(f'{cert} {p}: core value not tagged in any Lean declaration')
    # source anchors of numbers that exist only in the notes and scripts
    decls = lean_decls()
    anchored = set()
    for module, decl, path, first, last, anchor, lit in LINES:
        anchored.add((module, decl))
        where = f'LINES {module}.{decl} {path}:{first}-{last}'
        try:
            lines = (Path(roots[module]) / path).read_text().split('\n')
        except FileNotFoundError:
            errors.append(f'{where}: file not found'); continue
        if not 1 <= first <= last <= len(lines):
            errors.append(f'{where}: out of range')
        elif norm(anchor) not in norm(' '.join(lines[first - 1:last])):
            errors.append(f'{where}: anchor {anchor!r} missing')
        if (module, decl) not in decls:
            errors.append(f'{where}: declaration not found')
        elif not has_token(decls[(module, decl)], lit):
            errors.append(f'{where}: Lean literal {lit!r} not in the declaration')
    for module, decl, text in USES:
        if (module, decl) not in decls:
            errors.append(f'USES {module}.{decl}: declaration not found')
        elif not has_token(decls[(module, decl)], text):
            errors.append(f'USES {module}.{decl}: {text!r} not in the declaration')
    # a definition whose body is a numeric expression, or a numeric field of a `Params`
    # instance, restates a source value and must carry a tag or a LINES row
    numeric = re.compile(r'^[\s\d/()*^+-]*\d[\s\d/()*^+-]*,?\s*(?:--.*)?$')
    for f in sorted(LEAN.glob('*.lean')):
        lines = f.read_text().split('\n')
        for n, line in enumerate(lines, 1):
            m = re.match(r'^(?:def (\S+) : \S+ :=|\s+(?:τ|σ|ε|c|lam|lamp|κ|β|δ|C1) :=)(.*)$', line)
            if not m:
                continue
            body, at_line = m.group(2), line
            if not body.strip() and n < len(lines):
                body, at_line = lines[n], lines[n]
            if (not numeric.match(body) or TAG.search(at_line) or AUDIT.search(at_line)
                    or (f.stem, m.group(1)) in anchored):
                continue
            errors.append(f'{f.name}:{n}: numeric definition without a json tag or LINES row')
    for pr, path in SHARED:
        base = HERE / 'data' / 'pr5' / path
        copy = HERE / 'data' / pr / path
        if hashlib.sha256(base.read_bytes()).digest() != hashlib.sha256(copy.read_bytes()).digest():
            errors.append(f'{pr}/{path} differs from pr5/{path}')
    for f in sorted(LEAN.glob('*.lean')) + [HERE.parent / 'lean' / 'PRChecksB.lean']:
        code = strip_comments(f.read_text())
        for pat, name in FORBIDDEN:
            if pat.search(code):
                errors.append(f'{f.name}: contains {name}')
    return errors, count, seen


def selftest(roots):
    """Perturb one tagged value per certificate and expect exactly that failure."""
    problems = []
    _, _, seen = check(roots)
    for root, cert in sorted({(r, c) for r, c, _ in seen}):
        path = sorted(p for r, c, p in seen if (r, c) == (root, cert))[0]
        value = at(json.loads((Path(root) / 'certificates' / cert).read_text()), path)
        bumped = str(Fraction(str(value)) + Fraction(1, 10 ** 30))
        errs, _, _ = check(roots, {(root, cert, path): bumped})
        hits = [e for e in errs if f'{cert} {path} =' in e]
        if not hits or len(errs) != len(hits):
            problems.append(f'selftest: perturbing {cert} {path} gave {errs}')
    return problems


def main(argv):
    roots = dict(MODULES)
    for arg in argv:
        if '=' in arg and not arg.startswith('--'):
            k, v = arg.split('=', 1)
            roots[k] = v
    errors, count, seen = check(roots)
    if '--selftest' in argv and not errors:
        errors += selftest(roots)
    if errors:
        print('\n'.join(errors))
        print(f'FAIL: {len(errors)} problem(s)')
        return 1
    certs = sorted({c for _, c, _ in seen})
    print(f'OK: {count} tagged Lean literals equal their certificate values '
          f'({len(seen)} distinct keys in {", ".join(certs)}); all core values tagged; '
          f'no sorry/admit/native_decide/axiom' + ('; selftest passed' if '--selftest' in argv else ''))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
