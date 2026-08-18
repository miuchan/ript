# Ript

**Kern-kontrolita fundamento en Lean 4 por rimed-indicitaj procezteorioj.**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Kvalita kontrolpordo](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![Esplora stato](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript formaligas **Resource-Indexed Information Process Theory**: tiphavitajn
procezojn kies konduto kaj rimeduzo kunmetiĝas. Ĝi kunligas plenumeblajn
modelojn kun kern-kontrolitaj pruvoj pri kostlimoj, ĝusteco, relativa
kompleteco kaj struktur-konserva semantiko.

> [!IMPORTANT]
> Ript estas frustadia esplora programaro. Lean-kerno kontrolas la kompilitajn
> rezultojn, sed la publika API ne estas stabila kaj la projekto ne pretendas
> esti kompleta teorio de fizika informado.

## Kial Ript?

Ordinaraj procezteorioj priskribas kiuj procezoj kunmetiĝas. Rimed-sentema
teorio devas ankaŭ klarigi la koston de kunmeto, kiuj reskriboj konservas tiun
koston kaj kiam sintaksa takso estas semantike valida.

Ript igas tiujn devojn eksplicitaj:

- rimedoj formas ordigitan adician algebron;
- sinsekva kaj paralela kunmetoj havas pruvitajn suprajn limojn;
- plenumebla sintakso restas aparta de kvocientaj pruvmodeloj;
- interpretoj konservas tipojn, ekvaciojn kaj deklaritajn rimedlimojn;
- determinismaj, stokastaj, komputaj, kaŭzaj, termikaj kaj kvantumaj modeloj
  realigas la komunajn interfacojn;
- ĉiu ĉefa teoremo havas registritan kontrolon de kernaj supozoj.

La nomo **Ript** mallongigas **Resource-Indexed Information Process Theory**.

## Kio estas realigita

### La formala kerno

- ordigitaj adiciaj rimedoj, buĝetoj, monotoneco kaj kostfiltradoj;
- kosthavaj kategorioj kun sinsekva kaj paralela kunmeto;
- plenumebla sinsekva kaj simetria monoida sintakso;
- eksplicitaj derivaĵoj, ĝusteco, termmodeloj, relativa kompleteco kaj monoida
  komenceco.

### Ekzaktaj finiaj modeloj

- finiaj funkcioj kaj mezuritaj totalaj/partaj komputoj;
- ekzaktaj finiaj stokastaj kanaloj super nenegativaj racionaloj;
- Kleisli-prezento per finiaj distribuoj kaj fidela ponto al `Stoch`;
- Blackwell-komparo, ekzakta finia Bayes-risko kaj task-rilata semantika valoro;
- finiaj DAG-kaŭzaj modeloj kun normaligitaj malmolaj intervenoj;
- finiaj Gibbs-konservaj sistemoj, KL/liberenergiaj rezultoj kaj plenumeblaj
  Landauer-atestantoj;
- fini-dimensiaj Kraus-kanaloj kaj fidela klasika senkoheriga enigo.

### Pli alta organizado kaj interna univalenta limo

- dukategorio de rimed-indicitaj simetriaj monoidaj procezmodeloj;
- kostekzaktaj modele-ekvivalentoj, ordinara homotopia lokigo kaj netrivialaj
  walking-localization ekzemploj;
- senaksioma profunde enigita sintakso por internaj idento kaj ekvivalento;
- grupoidaj, kvocientaj, antaŭfaskaj, simpliciaj nervaj kaj klasifik-diagramaj
  semantikoj;
- eksplicite 0/1-tranĉita amplekso, sen identigi arbitran Lean-ekvivalenton kun
  Lean-egaleco.

Por ekzaktaj kapabloj, limoj kaj teoremstatoj, uzu la
[modelmatricon](../MODEL_MATRIX.md), [esploran staton](RESEARCH_STATUS.md) kaj
[formalan projektskizon](../BLUEPRINT.md). Tiuj estas la aŭtoritataj registroj;
ĉi tiu paĝo intence restas superrigardo.

## Rapida komenco

Necesas Git, POSIX-ŝelo kaj [elan](https://github.com/leanprover/elan).

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

Antaŭ proponi ŝanĝon, rulu la tutan kvalitan kontrolpordon:

```bash
./scripts/quality-gate.sh
```

Plenumeblaj fin-al-finaj ekzemploj povas esti rulitaj rekte:

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

La [komenca gvidilo](GETTING_STARTED.md) enhavas la plenan ekzemplomapon,
unuopajn kontrolojn kaj problemsolvadon.

## Uzi Ript kiel Lean-dependaĵon

Ĝis ekzistas etikedita eldono, fiksu plenan commit-SHA:

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

Importu la plej malgrandan bezonatan modulon:

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

## Dokumentaro

- [Dokumentara centro](README.md): la plej mallonga vojo por ĉiu tasko.
- [Komenca gvidilo](GETTING_STARTED.md): instalado, ekzemploj, dependeco kaj
  problemsolvado.
- [Arkitekturo](ARCHITECTURE.md): tavoloj, dependodirekto kaj plenumebla/pruva
  limo.
- [Esplora stato](RESEARCH_STATUS.md): realigitaj bazoj, aktiva fronto kaj
  eksplicite nepretendataj rezultoj.
- [Modelkapabla matrico](../MODEL_MATRIX.md): nur realigitaj kaj kompilitaj
  kapabloj.
- [Formala projektskizo](../BLUEPRINT.md): teorema dependografeo kaj preciza
  stato.
- [Aksioma inventaro](../AXIOMS.md): kontrolita `#print axioms` eligo.
- [Konjekta registro](../CONJECTURES.md): malfermaj kaj lastatempe solvitaj
  asertoj.
- [Kontribua gvidilo](../CONTRIBUTING.md): deviga pruva kaj kvalita politiko.

La detalaj teknikaj dokumentoj uzas la anglan kiel ununuran fonton de vero.
Lean-deklaroj, la projektskizo, modelmatrico kaj aksioma kontrolo ne dependas de
naturalingva traduko.

## Fido kaj reprodukteblo

Ript malpermesas pruvajn anstataŭaĵojn, projektajn aksiomojn,
kompilil-fidajn eskapojn, `unsafe`-deklarojn kaj ĝeneralajn `import Mathlib` en
bibliotekaj moduloj. CI rekonstruas per fiksitaj Lean kaj Mathlib kaj traktas
avertojn kiel erarojn.

La realaj dependecoj de teoremoj uzantaj kvocientan validecon, propozician
etendeblecon aŭ klasikan elekton estas registritaj en
[AXIOMS.md](../AXIOMS.md).

## Nuna esplora fronto

La aktiva pli-kategoria fronto estas la arbitra, nedisigebla dudimensia
walking-localization-faktorigo. Objektoj, 1-morfismoj, 2-morfismoj,
identec-komparo, kunmet-komparo kaj naturaj datumoj por ĉiuj sagoj jam
kompiliĝas. La maldekstra unuleĝo ankaŭ kompiliĝas por ĉiu kanona antaŭenira
celsago. Ĝia invers-saga branĉo, la plena dekstra unuleĝo, oplaksa asocieco,
pseŭdofunktora pakado kaj la rezulta adjunkta-ekvivalenta faktorigo restas
malfermaj.

Ĝeneralaj mezureblaj kaŭzaj modeloj, Mathlib-denaska complete-Segal-space
interfaco kun malfortaj ekvivalentoj kaj plena dukategoria aŭ Dwyer–Kan lokigo
ankaŭ restas malfermaj. Vidu la [esploran staton](RESEARCH_STATUS.md).

## Kontribuado

Kontribuoj devas konservi la pruvlimon kaj deklari nur la efektive pruvitan
forton. Legu [CONTRIBUTING.md](../CONTRIBUTING.md), rulu
`./scripts/quality-gate.sh`, kaj ĝisdatigu la projektskizon kaj aksioman
inventaron kiam ĉefa teoremo ŝanĝiĝas.

## Versio, citado kaj permesilo

La Lake-paka versio estas `0.1.0`; ankoraŭ ne ekzistas stabila API. Esploraj
artefaktoj registru la plenan uzitan commit-SHA. Ript ankoraŭ ne havas arkivan
artikolon aŭ DOI; citu la deponejan adreson kaj fiksitan commit.

Neniu malfermfonta permesilo ankoraŭ estas elektita. Publika fontkodo sola ne
donas permeson kopii, redistribui aŭ krei derivaĵojn ĝis permesila dosiero estos
aldonita.

## Dankoj

Ript estas konstruita per [Lean 4](https://lean-lang.org/) kaj
[Mathlib](https://github.com/leanprover-community/mathlib4).
