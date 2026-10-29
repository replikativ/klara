#!/usr/bin/env python3
"""One sequential process driver. No third-party Python dependencies."""
import argparse, csv, datetime, hashlib, json, os, pathlib, random, shutil
import subprocess, sys, tempfile, time
ROOT = pathlib.Path(__file__).resolve().parents[2]
os.chdir(ROOT)
p = argparse.ArgumentParser()
p.add_argument('--out', default='experiments/pldi/results')
p.add_argument('--runs', type=int, default=10)
a = p.parse_args()
if a.runs < 10:
    p.error('confirmatory runs require at least ten independent JVMs per configuration')
out = pathlib.Path(a.out).resolve()
if out.exists():
    p.error('output directory already exists; choose a fresh --out to preserve raw evidence')
out.mkdir(parents=True)
child = None

def command(cmd, log):
    global child
    started = time.monotonic()
    print('Running:', ' '.join(map(str, cmd)), flush=True)
    with (out / log).open('w') as f:
        child = subprocess.Popen(list(map(str, cmd)), stdout=f, stderr=subprocess.STDOUT)
        try:
            code = child.wait()
        finally:
            if child.poll() is None:
                child.terminate()
                try: child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    child.kill(); child.wait()
            child = None
    if code:
        raise RuntimeError(f'{log}: exit {code}; see {out/log}')
    return time.monotonic()-started

def capture(cmd):
    r = subprocess.run(cmd, text=True, capture_output=True)
    return {'exit': r.returncode, 'stdout': r.stdout, 'stderr': r.stderr}

# Clojure classpath preparation may itself start a JVM, so it too precedes
# every test/benchmark. subprocess.run/wait always joins before the next one.
manifest = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'commit': capture(['git', 'rev-parse', 'HEAD']),
            'git_status': capture(['git', 'status', '--porcelain']),
            'uname': capture(['uname', '-a']), 'cpu': capture(['lscpu']),
            'memory': pathlib.Path('/proc/meminfo').read_text(),
            'cpu_governors': {str(x): x.read_text().strip() for x in
                              pathlib.Path('/sys/devices/system/cpu').glob('cpu[0-9]*/cpufreq/scaling_governor')},
            'protocol': {'runs': a.runs, 'order_seed': 162027, 'bootstrap_seed': 162028,
                         'bootstrap_resamples': 10000, 'jvm_heap': '512m', 'gc': 'SerialGC',
                         'kernel_sizes': [200, 2000], 'smc_particles': 32, 'smc_observations': 12,
                         'smc_microsteps_per_observation': 16, 'direct_linking': False,
                         'kernel_warmup': {'t0':100, 'others':10000},
                         'smc_warmup': 5, 'smc_measured':7},
            'source_sha256': {str(x): hashlib.sha256(x.read_bytes()).hexdigest()
                              for base in ['src', 'test', 'test-spec', 'spec', 'experiments/pldi', 'experiments/compiler']
                              for x in pathlib.Path(base).rglob('*')
                              if x.is_file() and out not in x.resolve().parents
                              and x.suffix in ['.clj', '.edn', '.java', '.py', '.sh']}}
(out/'manifest.json').write_text(json.dumps(manifest, indent=2))
try:
    command(['clojure','-J-Xmx2g','-J-XX:+UseSerialGC','-X:test'], 'tests.txt')
    if '0 failures, 0 errors.' not in (out/'tests.txt').read_text():
        raise RuntimeError('full test summary is not green')
    command(['clojure','-J-Xmx2g','-J-XX:+UseSerialGC','-M:spec-diff',
             'experiments/pldi/spec.clj',out], 'spec-diff.txt')
    command(['clojure','-J-Xmx512m','-J-XX:+UseSerialGC','-Sdeps','{:aliases {:pldi {:main-opts []}}}', '-M:test:pldi',
             'experiments/pldi/scale.clj',out], 'generated.txt')
    with tempfile.TemporaryDirectory(prefix='klara-s16-') as classes:
        command(['javac','-J-Xmx128m','-d',classes,
                 'experiments/compiler/java/klara/bench/Baselines.java','experiments/pldi/Smc.java'], 'javac.txt')
        order=[]; rng=random.Random(162027)
        for repeat in range(a.runs):
            modes=['t0','compiled','clojure','java']; rng.shuffle(modes)
            for mode in modes:
                name=f'run-{repeat:02d}-{mode}'; order.append(name)
                elapsed=command(['clojure','-J-Xmx512m','-J-XX:+UseSerialGC',
                                 '-J-Dclojure.compiler.direct-linking=false',
                                 '-Sdeps','{:paths ["src" "'+classes+'"]}',
                                 '-M','experiments/pldi/entry.clj',mode,out/name], name+'.txt')
                manifest.setdefault('elapsed_seconds',{})[name]=elapsed
                manifest['order']=order
                (out/'manifest.json').write_text(json.dumps(manifest,indent=2))
    manifest['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2))
    command(['clojure','-J-Xmx256m','-M','experiments/pldi/summarize.clj',out], 'summarize.txt')
    subprocess.run([sys.executable,'experiments/pldi/render.py',out],check=True)
except BaseException:
    manifest['incomplete']=True
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2))
    raise
