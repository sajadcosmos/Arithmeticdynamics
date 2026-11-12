import re, glob, os
import json, sys
here=os.path.dirname(os.path.abspath(__file__))
root=os.path.join(here,'..','ArithmeticDynamics')
files={os.path.basename(f)[:-5]:open(f).read().split('\n') for f in glob.glob(root+'/*.lean')}
def find(name):
    pat=re.compile(r'^(noncomputable )?(def|abbrev|structure|theorem) '+re.escape(name)+r'(\s|$)')
    for fn,lines in files.items():
        for i,l in enumerate(lines):
            if pat.match(l): return fn,i,lines
    raise KeyError(name)
def expand(name):
    if '*' not in name: return [name]
    rx=re.compile('^'+re.escape(name).replace(r'\*','[A-Za-z0-9_\']*')+'$')
    out=[]
    for fn,lines in files.items():
        for l in lines:
            m=re.match(r"^theorem ([A-Za-z0-9_'.]+)",l)
            if m and rx.match(m.group(1)): out.append(m.group(1))
    return sorted(set(out))
def extract(name, is_def=False):
    fn,i,lines=find(name)
    # docstring
    j=i-1
    while j>=0 and lines[j].startswith('omit'): j-=1
    doc=[]
    if j>=0 and lines[j].rstrip().endswith('-/'):
        k=j
        while not lines[k].lstrip().startswith('/--'): k-=1
        doc=lines[k:j+1]
    body=[]
    k=i
    while k<len(lines):
        l=lines[k]
        if is_def:
            if l.strip()=='' : break
            body.append(l)
        else:
            if ':= by' in l or (l.rstrip().endswith(':=') and not re.search(r'\blet\s',l)):
                body.append(re.sub(r'\s*:=( by)?\s*$','',l)); break
            if re.search(r':=\s*\S',l) and not re.search(r'\blet\s|haveI|\bhave\s',l):
                body.append(l.split(':=')[0].rstrip()); break
            body.append(l)
        k+=1
    return fn,i+1,'\n'.join(doc+body)

rows_data=json.load(open(os.path.join(here,'statement_rows.json')))
rows=[(r['result'],[(x['name'],x.get('hyp')) for x in r['lean']]) for r in rows_data]
def resname(r): return r
defs=[('unitaryCayley','The unitary Cayley graph X_n as a Mathlib SimpleGraph on ZMod n: a ~ b iff a - b is a unit (Section 2.2).'),
('adj','Adjacency operator of X_n: (Af)(i) = Σ_{u unit} f(i+u).'),
('lap','Laplacian of X_n on complex vectors: L = φ(n) I - A.'),
('lapR','The same Laplacian on real vectors.'),
('ramanujan','Ramanujan sum c_n(j) = Σ_{u unit} e(uj/n).'),
('r','r(M) = μ(M)/φ(M), equation (2.1).'),
('lapEig','Laplacian eigenvalue λ(k) = φ(n)(1 - r(ord k)), equation (2.4).'),
('IsSymm','Symmetric connection set S = -S.'),
('cLap','Laplacian of a general circulant Cay(Z_n, S).'),
('cSym','Fourier symbol C_S(k), equation (2.2).'),
('gcdSet','Connection set S_D = {s : gcd(s,n) ∈ D} of the gcd graph X_n(D).'),
('ProperDivisors','D consists of proper divisors of n (Section 2.3: n ∉ D).'),
('lam2','λ₂ of a circulant = min over k ≠ 0 of |S| - C_S(k).'),
('avg','Average of a vector.'),('err','Consensus error x - x̄1.'),('sqNorm','Squared Euclidean norm.'),
('step','One step x ↦ (I - εL)x of the consensus iteration on X_n (equation (4.1)).'),
('cStep','One step x ↦ (I - εL_S)x of the consensus iteration on a circulant.'),
('DivSet','The set {r(M) : M | n, M > 1} of normalised non-trivial adjacency eigenvalues.'),
('rateOf','(rmax - rmin)/(2 - rmax - rmin) = (λmax - λ₂)/(λmax + λ₂).'),
('IsRate','ρ is the optimal rate ρ*(X_n) (Definition 4.2).'),
('rhoStar','ρ*(X_m) as a function of m (0 for m < 2), used for the mean value.'),
('meanRate','The mean value of ρ* (series of Proposition 4.9).'),
('kuramotoField','Kuramoto vector field (5.1) on X_n with ω = 0.'),
('cField','Kuramoto vector field (5.1) on a general circulant.'),
('twisted','The twisted state θ_j = 2π a j/n.'),
('jac','Jacobian at a twisted state acting on complex vectors (Lemma 5.2).'),
('cJac','Jacobian at a twisted state of a circulant, real form.'),
('energy','Energy E (5.2), whose negative gradient is the Kuramoto field.'),
('g','The instability exponent g(M), equation (5.4).'),
('IsSolution','A solution of ẋ = F(x): differentiable, with derivative F(x(t)) for all t.'),
('LyapunovStable','Lyapunov stability of an equilibrium.'),
('ExpStableOnLevel','Local exponential stability with rate ρ on the invariant level set Σ x_i = Σ x*_i (stability modulo rotation).'),
('LyapunovIndirectStability','Hypothesis (H1).'),('LyapunovIndirectInstability','Hypothesis (H2).'),('AbsilKurdyka','Hypothesis (H3).'),
]
out=[]
out.append('''# Statement map: results of the paper and their Lean statements

This file lists, for every numbered result of the paper *Arithmetic dynamics on unitary Cayley and
GCD graphs*, the Lean theorems that prove it, with their exact statements (doc-comment and
signature, copied verbatim from the source; proofs omitted). Section A gives the definitions that
model the objects of the paper, so that each formal statement can be compared with the
mathematics. It was generated from the source of release v1.1 and can be regenerated with
`python3 tools/statements.py`.

Conventions. `ZMod n` is ℤ/n. Vectors on the vertex set are functions `ZMod n → ℝ` (or `ℂ`).
The theorems use `variable {n : ℕ} [NeZero n]`, i.e. n ≥ 1; a hypothesis `1 < n` or `2 ≤ n` is
added where the paper assumes n ≥ 2. Connectivity of `Cay(ℤ/n, S)` is the hypothesis
`AddSubgroup.closure (S : Set (ZMod n)) = ⊤` (S generates ℤ/n); `lam2_pos_iff` proves it is
equivalent to λ₂ > 0, and `gcd_connected_iff` proves that for gcd graphs it is equivalent to
gcd(D) = 1. Quotients are sometimes stated multiplied out (`x * v = u` for `x = u / v`).
Norm estimates are stated for squared norms, `‖e(t)‖² ≤ (ρ²)^t ‖e(0)‖²`, which is equivalent to
`‖e(t)‖ ≤ ρ^t ‖e(0)‖`. Theorems marked (H1)–(H3) take the corresponding classical theorem as an
explicit hypothesis (Section B).

Build and check:

```bash
lake exe cache get
lake build
lake env lean AxiomCheck.lean     # every theorem: [propext, Classical.choice, Quot.sound] or fewer
```
''')
out.append('## A. Definitions modelling the paper\n')
for nm,desc in defs:
    try: fn,ln,txt=extract(nm,True)
    except KeyError: continue
    out.append(f'### `{nm}` — {desc}\n\n`ArithmeticDynamics/{fn}.lean`, line {ln}\n\n```lean\n{txt}\n```\n')
out.append('## B. The classical hypotheses (H1)–(H3)\n\nThey are definitions of type `Prop`, not axioms, and appear as explicit arguments `(hL : LyapunovIndirectStability n)` etc. of the theorems that use them. Their statements are in Section A above. Each quantifies over every C¹, globally Lipschitz vector field on ℝ^{ℤ/n}.\n')
out.append('## C. Results of the paper\n')
seen=set()
for res,lst in rows:
    out.append(f'### {resname(res)}\n')
    seen_row=set()
    for nm,h in lst:
        for nm2 in expand(nm):
            if nm2 in seen_row or nm2=='lapEig_ge_half': continue
            seen_row.add(nm2)
            fn,ln,txt=extract(nm2)
            tag=f' — uses {h}' if h else ''
            out.append(f'`{nm2}` (`{fn}.lean`, line {ln}){tag}\n\n```lean\n{txt}\n```\n')
open(os.path.join(here,'..','STATEMENTS.md'),'w').write('\n'.join(out))
print(len(rows), sum(len(l) for _,l in rows))
