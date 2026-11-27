import random
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1
STACK_TOP = 0x10080000
EXIT = 0x20010000
CANARY = 0xa5a5a5a5a5a5a5a5
DUMP = 128
REGISTERS = ('rax', 'rcx', 'rbx', 'rdx', 'r8', 'r9')
NUMBER = {'rax': 0, 'rcx': 1, 'rdx': 2, 'rbx': 3, 'r8': 8, 'r9': 9}
PUSH = {'rax': [80], 'rcx': [81], 'rbx': [83], 'rdx': [82], 'r8': [65, 80], 'r9': [65, 81]}
POP = {'rax': [88], 'rcx': [89], 'rbx': [91], 'rdx': [90], 'r8': [65, 88], 'r9': [65, 89]}
ALU = {'add': [72, 1, 200], 'sub': [72, 41, 200], 'mul': [72, 15, 175, 193], 'and': [72, 33, 200],
       'or': [72, 9, 200], 'xor': [72, 49, 200], 'shl': [72, 211, 224], 'shr': [72, 211, 232]}
OTHER = {'xchg': [72, 145], 'cmp': [72, 57, 200], 'setb': [15, 146, 192], 'movzx': [72, 15, 182, 192],
         'test rax': [72, 133, 192], 'test rbx': [72, 133, 219], 'cmovne': [72, 15, 69, 193]}
NEAR = [[72, 133, 201], [72, 133, 210], [72, 199, 193, 1, 0, 0, 0], [72, 185, 1, 0, 0, 0, 0, 0, 0, 0],
        [72, 139, 132, 36, 8, 0, 0, 0], [72, 139, 68, 36, 4], [72, 139, 68, 36, 128], [72, 1, 201],
        [72, 211, 225], [72, 15, 68, 193], [15, 147, 192], [73, 137, 192], [72, 137, 199], [102, 144],
        [144], [72, 255, 192], [72, 41, 193], [235, 0], [116, 0], [72, 247, 216]]
EDGES = [0, 1, 2, 7, 63, 64, 65, 127, 128, 255, 256, (1 << 31) - 1, 1 << 31, (1 << 32) - 1, 1 << 32,
         (1 << 63) - 1, 1 << 63, MASK - 1, MASK]


def le(value, size):
    return list((value & ((1 << (8 * size)) - 1)).to_bytes(size, 'little'))


def move(dst, src):
    return [72 + (4 if NUMBER[src] >= 8 else 0) + (1 if NUMBER[dst] >= 8 else 0), 137,
            192 + 8 * (NUMBER[src] % 8) + NUMBER[dst] % 8]


def load(i, long=False):
    if i < 16 and not long:
        return [72, 139, 68, 36, 8 * i]
    return [72, 139, 132, 36] + le(8 * i, 4)


def forms(rng):
    out = [PUSH[r] for r in REGISTERS] + [POP[r] for r in REGISTERS]
    out += [move(d, s) for d in REGISTERS for s in REGISTERS]
    out += list(ALU.values()) + list(OTHER.values())
    out += [[72, 184] + le(rng.choice(EDGES + [rng.getrandbits(64)]), 8)]
    out += [[72, 199, 192] + le(rng.choice(EDGES + [rng.getrandbits(32)]), 4)]
    out += [load(rng.randrange(6)), load(rng.randrange(16, 20))]
    return out


def value(rng):
    return rng.choice(EDGES) if rng.randrange(3) else rng.getrandbits(64)


def state(rng, depth):
    regs = [value(rng) for _ in REGISTERS]
    flags = rng.randrange(3) | rng.randrange(3) << 2
    stack = [EXIT] + [value(rng) for _ in range(depth)]
    return regs, flags, stack


def record(regs, flags, stack, code):
    data = b''.join(struct.pack('<Q', r) for r in regs) + struct.pack('<Q', STACK_TOP)
    data += bytes([flags, len(stack)]) + b''.join(struct.pack('<Q', v) for v in stack)
    return data + struct.pack('<H', len(code)) + bytes(code)


def program(rng, fragments, misaligned):
    pieces = [rng.choice(fragments) for _ in range(rng.randrange(1, 12))]
    code = []
    for index, piece in enumerate(pieces):
        if rng.randrange(6) == 0:
            rest = sum(map(len, pieces[index:]))
            skip = rng.randrange(rest + 1) if misaligned else sum(map(len, pieces[index:index + rng.randrange(len(pieces) - index + 1)]))
            code += ([233] if rng.randrange(2) else [15, 132]) + le(skip, 4)
        code += piece
    return code + [195]


def cases(rng):
    out = []
    for _ in range(40):
        for piece in forms(rng):
            out.append(state(rng, rng.randrange(0, 20)) + (piece + [195],))
    for _ in range(6000):
        out.append(state(rng, rng.randrange(0, 12)) + (program(rng, forms(rng), False),))
    for _ in range(3000):
        out.append(state(rng, rng.randrange(0, 12)) + (program(rng, forms(rng), True),))
    for _ in range(3000):
        out.append(state(rng, rng.randrange(0, 12)) + (program(rng, forms(rng) + NEAR, rng.randrange(2) == 0),))
    for _ in range(2000):
        code = [rng.randrange(256) for _ in range(rng.randrange(1, 10))]
        out.append(state(rng, rng.randrange(0, 4)) + (code + [195],))
    return out


def model(batch, directory):
    data = b''.join(record(*case) for case in batch)
    assert len(data) <= 65536
    source, target = directory / 'cases', directory / 'results'
    source.write_bytes(data)
    subprocess.run([ROOT / '.build/remy', 'replay', source, target], check=True, capture_output=True, timeout=600)
    raw, at, results = target.read_bytes(), 0, []
    for _ in batch:
        if raw[at] == 0:
            results.append(None)
            at += 1
            continue
        address, = struct.unpack_from('<Q', raw, at + 1)
        regs = list(struct.unpack_from('<6Q', raw, at + 9))
        pointer, = struct.unpack_from('<Q', raw, at + 57)
        flags = raw[at + 65]
        depth, = struct.unpack_from('<H', raw, at + 66)
        stack = list(struct.unpack_from(f'<{depth}Q', raw, at + 68))
        results.append((address, regs, pointer, flags, stack))
        at += 68 + 8 * depth
    assert at == len(raw)
    return results


def hardware(batch, harness):
    data = b''.join(struct.pack('<I', len(r)) + r for r in (record(*case) for case in batch))
    raw = subprocess.run([harness], input=data, capture_output=True, check=True, timeout=600).stdout
    size = 1 + 17 * 8 + DUMP * 8
    assert len(raw) == size * len(batch)
    out = []
    for i in range(len(batch)):
        chunk = raw[i * size:(i + 1) * size]
        out.append((chunk[0], struct.unpack_from('<17Q', chunk, 1), struct.unpack_from(f'<{DUMP}Q', chunk, 137)))
    return out


def compare(case, expected, observed):
    regs, flags, stack, code = case
    address, mregs, pointer, mflags, mstack = expected
    status, out, memory = observed
    problems = []
    if status != 1:
        return [f'hardware trapped with signal {status - 64}']
    for name, want, got in zip(REGISTERS, mregs, out):
        if want != got:
            problems.append(f'{name} model {want:#x} hardware {got:#x}')
    for i in range(6, 15):
        if out[i] != 0x0101010101010101 * (i + 1):
            problems.append(f'unmodelled register {i} changed to {out[i]:#x}')
    if out[16] != pointer:
        problems.append(f'rsp model {pointer:#x} hardware {out[16]:#x}')
    zero, carry = mflags & 3, mflags >> 2
    if zero < 2 and (out[15] >> 6 & 1) != zero:
        problems.append(f'ZF model {zero} hardware {out[15] >> 6 & 1}')
    if carry < 2 and (out[15] & 1) != carry:
        problems.append(f'CF model {carry} hardware {out[15] & 1}')
    if list(memory[:len(mstack)]) != mstack:
        problems.append('stack contents differ')
    if pointer + 8 * len(mstack) != STACK_TOP + 8 * len(stack):
        problems.append('model frame top moved')
    if any(w != CANARY for w in memory[len(mstack):len(mstack) + 16]):
        problems.append('memory above the frame changed')
    return problems


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    with tempfile.TemporaryDirectory(prefix='silicon') as directory:
        directory = Path(directory)
        harness = directory / 'harness'
        subprocess.run(['cc', '-O1', '-no-pie', '-o', harness, ROOT / 'tests/silicon.c'], check=True)
        control = ([5, 3, 0, 0, 0, 0], 0, [EXIT], ALU['add'] + [195])
        expected, = model([control], directory)
        observed, = hardware([(control[0], control[1], control[2], ALU['sub'] + [195])], harness)
        assert compare(control, expected, observed), 'a substituted instruction went unnoticed'
        totals = {'cases': 0, 'model rejected': 0, 'returned elsewhere': 0, 'compared': 0, 'instructions': 0}
        failures = []
        for seed in range(count):
            rng = random.Random(0x5349 + seed)
            pending = cases(rng)
            while pending:
                batch, size = [], 0
                while pending and size + len(record(*pending[0])) <= 65536:
                    size += len(record(*pending[0]))
                    batch.append(pending.pop(0))
                expected = model(batch, directory)
                runnable = [(c, e) for c, e in zip(batch, expected) if e is not None and e[0] == EXIT]
                totals['cases'] += len(batch)
                totals['model rejected'] += sum(e is None for e in expected)
                totals['returned elsewhere'] += sum(e is not None and e[0] != EXIT for e in expected)
                observed = hardware([c for c, _ in runnable], harness) if runnable else []
                for (case, want), got in zip(runnable, observed):
                    totals['compared'] += 1
                    totals['instructions'] += len(case[3])
                    problems = compare(case, want, got)
                    if problems:
                        failures.append((case, problems))
        print(' '.join(f'{k}={v}' for k, v in totals.items()))
        for case, problems in failures[:20]:
            print(bytes(case[3]).hex(' '), '|', '; '.join(problems))
        assert not failures, f'{len(failures)} executions differ from the model'
        assert totals['compared'] > 10000
        print('every model-accepted execution matched the host CPU')


if __name__ == '__main__':
    main()
