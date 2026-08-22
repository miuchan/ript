# Komenca gvidilo

[English](../en/GETTING_STARTED.md) · [简体中文](../zh-CN/GETTING_STARTED.md) ·
[日本語](../ja/GETTING_STARTED.md) · [Esperanto](GETTING_STARTED.md)

Ĉi tiu gvidilo kondukas freŝan kopion de la deponejo de instalado de la ilaro
ĝis kontrolita konstruo, kaj poste montras reprezentajn ruleblajn modelojn.

## Antaŭkondiĉoj

Instalu:

- Git;
- POSIX-kongruan ŝelon;
- [elan](https://github.com/leanprover/elan), la administrilon de Lean-ilĉenoj.

La deponejo fiksas Lean en `lean-toolchain` kaj Mathlib en `lakefile.lean` kaj
`lake-manifest.json`. Ne anstataŭigu ilin per alia tutmonde instalita Lean-versio.

## Kloni kaj konstrui

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

`lake exe cache get` elŝutas kongruajn antaŭkompilitajn Mathlib-artefaktojn se
ili ekzistas. `lake build` poste kompilas la tutan bibliotekon `Ript` kaj traktas
Lean-avertojn kiel erarojn.

## Ruli la kvalitan kontrolon

```bash
./scripts/quality-gate.sh
```

La kontrolo plenumas, laŭorde:

1. regulojn pri fontoj kaj dokumentaro;
2. kontrolon de la radika modul-kovrado;
3. plenan kernan konstruon;
4. kontrolon de deklaroj;
5. asertojn pri ruleblaj ekzemploj;
6. la permesliston de kernaj supozoj.

Por fokusita ripetado uzu la unuopajn komandojn:

```bash
./scripts/check-source-quality.sh
lake exe mk_all --check
lake build
lake env lean Ript/Audit/Lint.lean
./scripts/check-examples.sh
./scripts/check-axioms.sh
```

La plena kontrolo restas deviga antaŭ kunfando de tirpeto.

## Esplori ruleblajn ekzemplojn

Ĉiu suba ekzemplo estas ordinara Lean-modulo: ĝia rulado kontrolas ĉiujn
deklarojn kaj montras la rezultojn de `#eval`.

Kernaj rimedoj kaj funkcioj:

```bash
lake env lean Ript/Examples/BitProcesses.lean
lake env lean Ript/Examples/CostFiltration.lean
lake env lean Ript/Examples/ClassicalCopy.lean
```

Ekzaktaj stokastaj kaj decidaj modeloj:

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/KleisliBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/StochasticSeparation.lean
```

Komputado kaj kaŭzeco:

```bash
lake env lean Ript/Examples/SimpleComputation.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

Termodinamiko:

```bash
lake env lean Ript/Examples/SimpleThermalModel.lean
lake env lean Ript/Examples/ApproximateErasure.lean
lake env lean Ript/Examples/ExactWorkCycle.lean
```

Kvantuma kaj interne univalenta semantiko:

```bash
lake env lean Ript/Examples/QubitChannel.lean
lake env lean Ript/Examples/UnivalentProcessUniverse.lean
lake env lean Ript/Examples/UnivalentSimplicial.lean
```

`scripts/check-examples.sh` devigas la atendatajn elirojn; la ekzemploj ne estas
nur prozaj fragmentoj.

## Uzi Ript kiel dependecon

Ript ankoraŭ ne publikigas stabilajn etikedajn versiojn. Fiksu plenan commit-SHA:

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

Post ŝanĝo de `lakefile.lean`, rulu:

```bash
lake update ript
lake exe cache get
lake build
```

Preferu mallarĝajn importojn:

```lean
import Ript.Resource.Budget
import Ript.Core.CostedProcess
import Ript.Models.FiniteStochastic
```

La ĝenerala `import Ript` estas oportuna por esplorado, sed intence pli vasta.

## Reproduktebla esploruzo

Registru en ĉiu artefakto:

- la plenan Ript-commit-SHA;
- la enhavon de `lean-toolchain`;
- la Mathlib-revizion el `lake-manifest.json`;
- la ekzaktan validigan komandon;
- la kontrolitajn supozojn de la teoremo laŭ `AXIOMS.md`.

La pakaĵa versio sola ne sufiĉas dum la API restas nestabila.

## Problemsolvado

### Malkongrua Lean-versio

Rulu `elan show` en la radiko. Elan devas elekti la ilĉenon el
`lean-toolchain`; se ne, riparu elan antaŭ ol ŝanĝi dosierojn de la deponejo.

### Mankas kompilitaj Mathlib-artefaktoj

Rerulu `lake exe cache get`. Se ne ekzistas kaŝmemoro por la platformo,
`lake build` povas kompili la dependecojn loke kaj bezonos pli da tempo.

### Fiasko de radika modul-kovrado

Ĉiu publika realiga modulo devas esti importita de `Ript.lean`. Aldonu la
mallarĝan importon kaj rerulu `lake exe mk_all --check`.

### Fiasko de la aksioma permeslisto

Ne malfortigu la skripton. Rulu la koncernan `#print axioms`, kontrolu ĉu la
dependeco estas atendata, kaj ĝisdatigu `Ript/Audit/AxiomChecks.lean` kaj
`AXIOMS.md` nur kiam la teoremo kaj ĝia fidolimo vere ŝanĝiĝis.

### Ŝanĝita rulebla ekzemplo

Unue esploru la semantikan ŝanĝon. Ĝisdatigu `scripts/check-examples.sh` nur
se la nova eliro estas intenca kaj pruvita de la koncerna ekzempla modulo.

## Plua legado

- [Arkitekturo](ARCHITECTURE.md)
- [Esplora stato](RESEARCH_STATUS.md)
- [Formala plano](reference/BLUEPRINT.md)
- [Kontribua gvidilo](CONTRIBUTING.md)
- [Regado](GOVERNANCE.md) kaj [Sekureco](SECURITY.md)
