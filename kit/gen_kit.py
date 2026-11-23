#!/usr/bin/env python3
# Generate Kit.lean: the machine library of brilliant-hq/pequalnp-proofs
# (lean/PEqualNP/Library/Machines, Apache-2.0) inlined into one file that imports only
# Mathlib and PEqualNP.Defs and obeys the plain-file rules of an outside proof file.
#
#   python gen_kit.py <machines dir> <out file> [namespace, default PEqualNP.Outside.Kit]
#
# What it does, per module in import order: drops the imports, strips every comment,
# renames the namespace PEqualNP.Library.Machines to PEqualNP.Outside.Kit (opening
# PEqualNP.Library after each namespace line), replaces each finite enum `inductive` and
# its Fintype `instance` with `Fin n` (constructors become typed literals), expands the
# local notation `stp`, turns `@[reducible] def` into `abbrev`, and rewrites the few
# `cases`/`rcases` proofs on those enums to `fin_cases`.
import re
import sys

MODULES = [
    'Run', 'Compose', 'ComposeRun', 'ComposeTime', 'FilterMap', 'TwoPass',
    'First', 'FirstRun', 'FirstPoly', 'Pairing', 'Mul', 'Clock', 'FirstTime',
    'Iter', 'IterRun', 'IterMeasure', 'ConstList', 'Const', 'Reverse', 'LenLE',
    'ReduceNP', 'AllTrue', 'SquareClock', 'Transducer', 'FirstG', 'FirstGRun', 'ExpPad',
]

# enum types: module -> [(type, [constructors])]
ENUMS = {
    'TwoPass': [('TPK', ['inp', 't1', 't2', 't3', 'out']), ('TPL', ['a', 'b', 'c', 'e'])],
    'First': [('FX', ['I', 'W', 'T', 'O']), ('FL', ['l1', 'l2', 'l3', 'l4', 'l5'])],
    'Iter': [('IX', ['I', 'C', 'T', 'O']), ('IL', ['l1', 'l2', 'l3', 'l4', 'l5', 'l6'])],
    'Mul': [('MulK', ['I', 'A', 'B', 'C', 'O']), ('MulL', ['split', 'outer', 'copy', 'back', 'clean'])],
    'LenLE': [('LL', ['split', 'cmp', 'eraseA', 'eraseB'])],
    'ExpPad': [('PadK', ['I', 'S', 'A', 'B', 'O']), ('PadL', ['start', 'outer', 'dbl', 'back', 'unsave', 'fin'])],
    'Transducer': [('TrK', ['inp', 'tmp', 'out'])],
    'FirstG': [('FX', ['I', 'W', 'TA', 'TB', 'O']), ('FL', ['l1', 'l2', 'l3', 'l4', 'l5'])],
}
# modules that use the enums of earlier modules: module -> [declaring modules]
ENUM_USERS = {
    'FirstRun': ['First'], 'FirstPoly': ['First'], 'Pairing': ['First', 'TwoPass'],
    'IterRun': ['Iter'], 'IterMeasure': ['Iter'], 'Clock': ['Mul'], 'FirstTime': ['First'],
    'SquareClock': ['TwoPass', 'Mul'], 'FirstGRun': ['FirstG'],
}

NOTATION = {
    'IterRun': ('stp', '(flip bind (TM2.step (iterProg M e₀ d₀ e₁)))'),
    'IterMeasure': ('stp', '(flip bind (TM2.step (iterProg M e₀ d₀ e₁)))'),
}


def strip_comments(src):
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
        elif src.startswith('/-', i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif src.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


def lit(t, cs, c):
    return f'({cs.index(c)} : {t})'


def replace_enums(mod, text):
    for t, cs in ENUMS.get(mod, []):
        # the inductive block (with deriving) and its Fintype instance
        text, k = re.subn(r'inductive ' + t + r'\b[^\n]*\n(?:[ \t]+[^\n]*\n)*', f'abbrev {t} : Type := Fin {len(cs)}\n', text)
        assert k == 1, (mod, t, 'inductive')
        text, k = re.subn(r'instance : Fintype ' + t + r' :=\n(?:[ \t]+[^\n]*\n)*', '', text)
        assert k == 1, (mod, t, 'instance')
    types = ENUMS.get(mod, []) + [e for src in ENUM_USERS.get(mod, []) for e in ENUMS[src]]
    for t, cs in types:
        for c in cs:
            text = re.sub(r'(?<![\w.])' + t + r'\.' + c + r'(?![\w\'])', lit(t, cs, c), text)
    # dotted shorthand `.c` in modules that declare the enum
    for t, cs in ENUMS.get(mod, []):
        for c in cs:
            text = re.sub(r'(?<=[\s(\[,⟨])\.' + c + r'(?![\w\'])', lit(t, cs, c), text)
    if mod in ENUMS or mod in ENUM_USERS:
        text = text.replace('funext k; cases k <;>', 'funext k; fin_cases k <;>')
        text = text.replace('; cases j <;> rfl', '; fin_cases j <;> rfl')
        text = re.sub(r'rcases j with j \| \(_(?: \| _)+\) <;> rfl',
                      'rcases j with j | j <;> [rfl; (fin_cases j <;> rfl)]', text)
        text = re.sub(r'rcases j with j \| \(_(?: \| _)+\)\n(  · [^\n]*\n)(?:  · [^\n]*\n)+',
                      r'rcases j with j | j\n\1  · fin_cases j <;> rfl\n', text)
    return text


def convert(mod, src, ns):
    text = strip_comments(src)
    text = '\n'.join(l for l in text.split('\n') if not l.startswith('import '))
    text = text.replace('PEqualNP.Library.Machines', ns)
    text = re.sub(r'^(namespace ' + re.escape(ns) + r'[\w.]*)$', r'\1\n\nopen PEqualNP.Library', text, flags=re.M)
    text = text.replace('@[reducible] def ', 'abbrev ')
    text = replace_enums(mod, text)
    if mod in NOTATION:
        name, body = NOTATION[mod]
        text, k = re.subn(r'^local notation [^\n]*\n', '', text, flags=re.M)
        assert k == 1, mod
        text = re.sub(r'(?<![\w.])' + name + r'(?![\w\'])', body, text)
    lines = [l.rstrip() for l in text.split('\n')]
    text = re.sub(r'\n{3,}', '\n\n', '\n'.join(lines)).strip('\n')
    return text + '\n'


def main():
    src_dir, out = sys.argv[1], sys.argv[2]
    ns = sys.argv[3] if len(sys.argv) > 3 else 'PEqualNP.Outside.Kit'
    parts = ['import Mathlib\nimport PEqualNP.Defs\n']
    for m in MODULES:
        with open(f'{src_dir}/{m}.lean', encoding='utf-8') as f:
            parts.append(convert(m, f.read(), ns))
    with open(out, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n'.join(parts))


if __name__ == '__main__':
    main()
