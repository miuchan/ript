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
kaj rimeduzo kunmetiĝas. Ĝi ligas plenumeblajn finiajn modelojn al kern-kontrolitaj
pruvoj pri rimedlimoj, solideco, kompletorezultoj kaj struktur-konserva semantiko.

> [!IMPORTANT]
> Ript estas frustadia esplora programaro. La kompilitaj rezultoj estas
> kern-kontrolitaj; la publika API kaj la esplora fronto ankoraŭ evoluas.

## Kio estas inkluzivita

- **Formalaj fundamentoj:** kosthavaj kategorioj, plenumebla sintakso,
  interpretoj, solideco, relativa kompleteco kaj monoida komenceco.
- **Ekzaktaj finiaj modeloj:** determinismaj, stokastaj, decidaj, komputaj,
  kaŭzaj, termikaj kaj kvantumaj ekzemploj.
- **Pli altaj strukturoj:** dukategorio de procezmodeloj, kost-ekzaktaj
  ekvivalentoj kaj walking-localization-konstruoj.
- **Kontroleblaj pruvoj:** CI rifuzas anstataŭilojn kaj nedokumentitajn
  supozojn; ĉefaj teoremoj havas eksplicitan aksiomliston.

La [matrico de modelkapabloj](../MODEL_MATRIX.md) listigas realigitajn ecojn.
La [esplora stato](RESEARCH_STATUS.md) apartigas pruvitajn, malfermajn kaj ne
pretendatajn rezultojn.

## Rapida komenco

Instalu [elan](https://github.com/leanprover/elan), poste rulu:

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

Antaŭ proponi ŝanĝon, rulu la plenan lokan kvalitan kontrolon:

```bash
./scripts/quality-gate.sh
```

Vidu la [komencan gvidilon](GETTING_STARTED.md) por postuloj, ekzemploj,
dependaĵa uzo kaj problemo-solvado.

## Dokumentaro

- [Dokumentara centro](README.md) — la plej mallonga vojo por ĉiu tasko.
- [Projekta amplekso kaj fidlimo](PROJECT_SCOPE.md) — dezajno, pretendoj,
  pruvpolitiko, matureco kaj permesilo.
- [Arkitekturo](ARCHITECTURE.md) — tavoloj kaj dependecaj limoj.
- [Esplora stato](RESEARCH_STATUS.md) — realigita, aktiva kaj malferma.
- [Formala plano](../BLUEPRINT.md) · [Aksioma inventaro](../AXIOMS.md) ·
  [Registro de konjektoj](../CONJECTURES.md) — aŭtoritataj esplorregistroj.

## Kontribuado

Legu la [kontribuan gvidilon](../CONTRIBUTING.md) kaj rulu
`./scripts/quality-gate.sh` antaŭ ol malfermi tirpeton.

Ript estas konstruita per [Lean 4](https://lean-lang.org/) kaj
[Mathlib](https://github.com/leanprover-community/mathlib4).
