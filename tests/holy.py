import json
import random
import socket
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from guest import image
from native import generate, source

ROOT = Path(__file__).resolve().parents[1]
SERIAL = b'''U0 SerPut(U8 *s)
{
  while (*s) {
    while (!(InU8(0x3FD)&0x20)) {}
    OutU8(0x3F8,*s++);
  }
}
U0 SerPrint(U8 *fmt,...)
{
  U8 *s=StrPrintJoin(NULL,fmt,argc,argv);
  SerPut(s);
  Free(s);
}
'''
CHECK = r'''#include "Shade.HC"
U64 Digest(U8 *bytes,I64 size)
{
  U64 h=14695981039346656037;
  I64 i;
  for (i=0;i<size;i++) h=(h^bytes[i])*1099511628211;
  return h;
}
U0 CheckAll()
{
  U8 *all=FileRead("Cases.TXT"),*p=all,*line;
  I64 index=0;
  Bool rows;
  F64 start;
  while (*p) {
    line=p;
    while (*p && *p!='\n') p++;
    if (*p) *p++=0;
    rows=FALSE;
    if (line[0]=='#') {
      rows=TRUE;
      line++;
    }
    start=tS;
    Translate(line,rows);
    SerPrint("@@C %d %d %d %X %.3f %s\n",index++,shade_ok,shade_size,Digest(shade_code,shade_size),tS-start,shade_report);
    Free(shade_code);
    Free(shade_report);
  }
  Free(all);
  SerPrint("@@DONE\n");
}
CheckAll;
'''


def digest(data):
    h = 14695981039346656037
    for b in data:
        h = ((h ^ b) * 1099511628211) & ((1 << 64) - 1)
    return h


def expected(text, rows, directory):
    path, out = directory / 'source', directory / 'out'
    path.write_text(text)
    out.unlink(missing_ok=True)
    command = [ROOT / '.build/remy', 'vectors', path, out] if rows else [ROOT / '.build/remy', path, out]
    result = subprocess.run(command, capture_output=True, text=True)
    data = out.read_bytes() if result.returncode == 0 else b''
    report = '' if rows else (result.stdout if result.returncode == 0 else result.stderr)
    return int(result.returncode == 0), len(data), digest(data), report.strip()


def main():
    if len(sys.argv) != 2 or not sys.argv[1]:
        raise SystemExit('usage: python3 tests/holy.py TempleOS.ISO')
    rng = random.Random(0x484F4C59)
    texts = [(ROOT / f'examples/{name}.remy').read_text().replace('\n', ' ') for name in ('Rings', 'Weave', 'Cells')]
    texts += [source(generate(rng, 6, ['x', 'y', 't'])) for _ in range(40)]
    texts += [source(generate(rng, 9, ['x', 'y', 't'])) for _ in range(4)]
    texts += ['(+ x', '(foo x y)', '(let 1 x x)', '(+ x y) z', '(* 18446744073709551615 x)', '(shl 1 18446744073709551616)']
    cases = [(t, False) for t in texts] + [(t, True) for t in texts[:3]]
    payload = ROOT / '.build/payload'
    files = {p.name: p.read_bytes() for p in payload.iterdir()}
    files['Check.HC'] = CHECK.encode()
    files['Cases.TXT'] = ''.join(('#' if rows else '') + t + '\n' for t, rows in cases).encode()
    files['Serial.HC'] = SERIAL
    files['Run.HC'] = b'#include "Check.HC"\nSerPut("@@END\\n");\n'
    once = b'Cd("::/");;\n#include "Serial.HC"\nSerPut("@@READY\\n");\n'
    with tempfile.TemporaryDirectory(prefix='holy') as directory:
        directory = Path(directory)
        iso, serial, monitor = directory / 'holy.iso', directory / 'serial', directory / 'qmp'
        image(Path(sys.argv[1]), iso, files, once)
        process = subprocess.Popen(['qemu-system-x86_64', '-m', '1024', '-smp', '2', '-accel', 'tcg,thread=multi',
            '-cdrom', iso, '-boot', 'd', '-display', 'none', '-monitor', 'none', '-no-reboot',
            '-chardev', f'socket,id=s,path={serial},server=on,wait=off', '-serial', 'chardev:s',
            '-qmp', f'unix:{monitor},server=on,wait=off'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            while not serial.exists() or not monitor.exists():
                time.sleep(0.1)
            connection = socket.socket(socket.AF_UNIX)
            connection.connect(str(serial))
            connection.settimeout(1)
            control = socket.socket(socket.AF_UNIX)
            control.connect(str(monitor))
            qmp = control.makefile('rwb', buffering=0)
            qmp.readline()
            qmp.write(b'{"execute":"qmp_capabilities"}\n')
            qmp.readline()

            def screen():
                qmp.write(json.dumps({'execute': 'screendump', 'arguments': {'filename': str(directory / 'shot.ppm')}}).encode() + b'\n')
                qmp.readline()
                return (directory / 'shot.ppm').read_bytes()

            output, began = bytearray(), time.monotonic()
            while b'@@READY' not in output:
                if time.monotonic() - began > 300:
                    raise RuntimeError('guest never became ready')
                try:
                    chunk = connection.recv(65536)
                except socket.timeout:
                    continue
                output += chunk
            time.sleep(3)
            keys = {' ': 'spc', '.': 'dot', '"': 'shift-apostrophe', '#': 'shift-3', '\n': 'ret'}
            for ch in '#include "Run.HC"\n':
                name = keys.get(ch) or ('shift-' + ch.lower() if ch.isupper() else ch)
                qmp.write(json.dumps({'execute': 'human-monitor-command',
                                      'arguments': {'command-line': f'sendkey {name} 40'}}).encode() + b'\n')
                qmp.readline()
                time.sleep(0.08)
            output, began = bytearray(), time.monotonic()
            while b'@@DONE' not in output and time.monotonic() - began < 1800:
                try:
                    chunk = connection.recv(65536)
                except socket.timeout:
                    continue
                output += chunk
                sys.stderr.write(chunk.decode('latin1'))
            if b'@@DONE' not in output:
                screen()
                (ROOT / '.build/holy.log').write_bytes(output)
                subprocess.run(['ffmpeg', '-v', 'error', '-y', '-i', directory / 'shot.ppm', ROOT / '.build/holy.png'])
                raise RuntimeError('guest did not finish; screen saved to .build/holy.png')
        finally:
            process.terminate()
            process.wait()
        lines = [l for l in output.decode('latin1').splitlines() if l.startswith('@@C ')]
        assert len(lines) == len(cases), (len(lines), len(cases))
        seconds, mismatches = 0.0, []
        for line, (text, rows) in zip(lines, cases):
            _, index, ok, size, value, elapsed, *report = line.split(' ')
            seconds += float(elapsed)
            got = (int(ok), int(size), int(value, 16), ' '.join(report).strip())
            want = expected(text, rows, directory)
            if got != want:
                mismatches.append((index, text[:60], want, got))
        for mismatch in mismatches:
            print('mismatch', *mismatch)
        assert not mismatches
        accepted = sum(1 for line in lines if line.split(' ')[2] == '1')
        print(f'{len(cases)} guest compilations matched the Poly/ML build byte for byte '
              f'({accepted} accepted, {len(cases) - accepted} rejected with identical reports, {seconds:.1f}s in TempleOS)')


if __name__ == '__main__':
    main()
