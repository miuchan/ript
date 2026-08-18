# Ript

**Kern-kontrolita Lean 4-fundamento por rimed-indicitaj procezteorioj.**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![Esplora stato](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript formaligas **Resource-Indexed Information Process Theory
(Rimed-Indicitajn Inform-Procezteoriojn)**: tipizitajn procezojn, kies konduto
kaj rimeduzo kunmetiĝas. Ĝi ligas plenumeblajn finiajn modelojn al
kern-kontrolitaj pruvoj pri kostlimoj, solideco, kompletorezultoj kaj
struktur-konserva semantiko.

> [!IMPORTANT]
> Ript estas frustadia esplora programaro. La kompilitaj rezultoj estas
> kontrolitaj de la Lean-kerno, sed la publika API ne estas stabila kaj la
> projekto ne pretendas kompletan teorion de fizika informo.

## Kial Ript

Ordinaraj procezteorioj diras, kiuj procezoj kunmetiĝas. Rimed-sentemaj teorioj
devas ankaŭ diri, kiel kostoj kunmetiĝas, kiuj reverkoj konservas ilin, kaj kiam
sintaksa takso estas semantike valida. Ript faras tiujn devojn eksplicitaj kaj
maŝinkontroleblaj.

- Orditaj adiciaj rimedoj spuras seriajn kaj paralelajn buĝetojn.
- Plenumebla sintakso restas aparta de kvocient-bazitaj pruvmodeloj.
- Interpretoj pruvas konservadon de tipoj, ekvacioj kaj rimedlimoj.
- Tensoro, kopiado, forĵeto, konvekseco, kaŭzeco kaj termodinamiko estas
  sendependaj kapabloj.
- Ĉiu ĉefa teoremo havas kontrolitan registron de siaj kernaj supozoj.

## Ĉefaj ecoj

- **Formala kerno:** kosthavaj kategorioj, plenumebla seria kaj monoida
  sintakso, solideco, relativa kompleteco kaj monoida komenceco.
- **Ekzaktaj finiaj modeloj:** determinismaj, stokastaj, decidaj, komputaj,
  kaŭzaj, termikaj kaj kvantumaj ekzemploj.
- **Pli alta organizado:** dukategorio de procezmodeloj, kost-ekzaktaj
  ekvivalentoj kaj kontrolitaj walking-localization-konstruoj.
- **Interna identeca semantiko:** senaksioma profunda sintakso kun grupoidaj,
  kvocientaj, antaŭfaskaj, simplecaj kaj klasifik-diagramaj interpretoj.

Vidu la [matricon de modelkapabloj](../MODEL_MATRIX.md) por realigitaj ecoj kaj
la [esploran staton](RESEARCH_STATUS.md) por precizaj limoj.

## Rapida komenco

Instalu [elan](https://github.com/leanprover/elan), poste rulu:

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

Antaŭ ol proponi ŝanĝon, rulu la plenan lokan CI-kontrakton:

```bash
./scripts/quality-gate.sh
```

Por rekte kontroli plenumeblan modelon:

```bash
lake env lean Ript/Examples/StochasticBits.lean
```

La [komenca gvidilo](GETTING_STARTED.md) kovras antaŭkondiĉojn, ekzemplojn,
dependaĵan agordon, reprodukteblon kaj problemo-solvadon.

## Uzi el Lean

Ĝis ekzistos markitaj eldonoj, fiksu plenan commit-SHA:

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

Preferu la plej malgrandan importon, kiu liveras la bezonatan API-on:

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

## Dokumentaro

- [Dokumentara centro](README.md) — task-bazitaj vojoj tra la projekto.
- [Komenca gvidilo](GETTING_STARTED.md) — konstrui, ruli kaj uzi Ript.
- [Arkitekturo](ARCHITECTURE.md) — tavoloj kaj dependecaj limoj.
- [Esplora stato](RESEARCH_STATUS.md) — pruvita, aktiva kaj ne pretendata.
- [Matrico de modelkapabloj](../MODEL_MATRIX.md) — kompilitaj kapabloj.
- [Formala plano](../BLUEPRINT.md) — teoremdependecoj kaj preciza stato.
- [Aksioma inventaro](../AXIOMS.md) — kontrolita `#print axioms` eligo.
- [Registro de konjektoj](../CONJECTURES.md) — malfermaj esplorpropozicioj.
- [Kontribua gvidilo](../CONTRIBUTING.md) — pruva kaj kvalita politiko.

## Fidolimo, stato kaj regado

Ript malpermesas pruvajn anstataŭilojn, projekt-specifajn aksiomojn,
kompilil-fidajn eskapojn kaj nesekurajn bibliotekajn deklarojn. CI fiksas la
Lean- kaj Mathlib-versiojn, traktas avertojn kiel erarojn, plenumas reprezentajn
modelojn kaj kontrolas la dokumentitan aksiomliston. Precizaj dependecoj estas
registritaj en [AXIOMS.md](../AXIOMS.md).

La aktiva fronto estas la arbitra dudimensia walking-localization-faktorigo.
Natureco por ĉiuj sagoj kaj ambaŭ plenaj unuleĝoj jam kompiliĝas; oplaksa
asocieco, pseŭdofunktora pakado kaj la fina adjunkta ekvivalento restas
malfermaj. Vidu la aŭtoritatan limon en
[RESEARCH_STATUS.md](RESEARCH_STATUS.md).

La Lake-pakaĵversio estas `0.1.0`; ankoraŭ ne ekzistas stabila API-eldono aŭ
arkiva DOI. Esploraj artefaktoj citu la deponejon kaj plenan commit-SHA. Neniu
malfermfonta permesilo ankoraŭ estas elektita; publika fontkodo sola ne donas
rajtojn de reuzo.

## Kontribuado

Kontribuoj estas bonvenaj kiam pretendoj kongruas kun la forto de kompilitaj
teoremoj kaj konservas la pruvlimon. Legu
[CONTRIBUTING.md](../CONTRIBUTING.md) kaj rulu `./scripts/quality-gate.sh` antaŭ
ol malfermi tirpeton.

Ript estas konstruita per [Lean 4](https://lean-lang.org/) kaj
[Mathlib](https://github.com/leanprover-community/mathlib4).
