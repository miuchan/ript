# Kontribui al Ript

[English](../en/CONTRIBUTING.md) · [简体中文](../zh-CN/CONTRIBUTING.md) ·
[日本語](../ja/CONTRIBUTING.md) · [Esperanto](CONTRIBUTING.md)

Ript traktas pruvan fidon, eksplicitajn dependecojn kaj reprodukteblan
komputadon kiel kunfandajn postulojn, ne nur reviziajn kutimojn.

## Deviga kvalita kontrolo

Rulu en la radiko de la deponejo:

```bash
./scripts/quality-gate.sh
```

La kontrolo rifuzas pruvtruojn, projektajn aksiomojn, nesekurajn deklarojn,
evitojn de kompilila fido, tro larĝajn `Mathlib`-importojn, implicitajn Lean-
identigilojn, malnovajn radikajn importojn, deklarajn erarojn, ŝanĝitan ruleblan
konduton, konstruajn avertojn kaj nedokumentitajn teoremajn supozojn. Poste ĝi
faras plenan kernan konstruon.

CI prezentas la samajn kontrolojn kiel `Lean quality gate`. Ŝanĝo estas preta
por kunfando nur kiam tiu tasko sukcesas.

## Politiko pri pruvoj kaj dependecoj

- metu nepruvitajn esplorasertojn en `CONJECTURES.md`, ne en teoremojn aŭ aksiomojn;
- importu la plej mallarĝajn praktikajn Mathlib-modulojn;
- konservu `set_option autoImplicit false` en ĉiu realiga modulo;
- aldonu ĉefajn teoremojn al `Ript/Audit/AxiomChecks.lean` kaj `AXIOMS.md`;
- se rulebla konduto intence ŝanĝiĝas, ĝisdatigu la aserton en
  `scripts/check-examples.sh` en la sama ŝanĝo.

## Dokumentara politiko

- konservu ĉiun logikan paĝon laŭ la sama relativa vojo sub `docs/en`,
  `docs/zh-CN`, `docs/ja` kaj `docs/eo`;
- ĝisdatigu ĉiujn kvar lingvojn kiam publika aserto, komando, stato aŭ fidolimo
  ŝanĝiĝas;
- konservu la radikajn `AXIOMS.md`, `BLUEPRINT.md`, `CONJECTURES.md` kaj
  `MODEL_MATRIX.md` kiel maŝinajn kanonajn registrojn;
- post ŝanĝo de la aksioma inventaro rulu
  `./scripts/sync-doc-reference-tables.sh` antaŭ la kvalita kontrolo.
