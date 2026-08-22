# Kontribui al Ript

[English](../en/CONTRIBUTING.md) · [简体中文](../zh-CN/CONTRIBUTING.md) ·
[日本語](../ja/CONTRIBUTING.md) · [Esperanto](CONTRIBUTING.md)

Ript akceptas kontribuojn pri pruvoj, modeloj, ekzemploj, dokumentoj kaj iloj.
Fido, eksplicitaj dependecoj, reprodukteblo kaj precizaj asertoj estas
kunfandaj postuloj.

## Antaŭ ol komenci

Legu [Amplekson](PROJECT_SCOPE.md), [Arkitekturon](ARCHITECTURE.md) kaj
[Esploran staton](RESEARCH_STATUS.md); serĉu issues kaj la
[konjektregistron](reference/CONJECTURES.md). Diskutu ŝanĝojn de amplekso,
publikaj teoremoj, arkitekturo, fiddependecoj, regado, sekureco aŭ permesilo
antaŭ realigo. Sekurecaj raportoj sekvas [Sekurecon](SECURITY.md).

## Laborfluo

```bash
git switch -c <focused-branch>
lake exe cache get
lake build <affected.module>
./scripts/quality-gate.sh
```

Tenu branĉojn kaj commit-ojn fokusaj. PR devas klarigi rezulton, kontroladon,
aksiomojn, kongruecon kaj restantajn limojn. Kunfando postulas verdan CI kaj
aprobon de la prizorganto.

## Pruva kaj realiga politiko

- neniuj pruvtruoj, projektaj aksiomoj, fid-evitoj aŭ unsafe-deklaroj;
- konservu `autoImplicit false` kaj mallarĝajn Mathlib-importojn;
- metu ĝeneralan mankantan bazon en `Ript/ForMathlib/`;
- tenu ruleblajn datumojn kontraŭflue de kvocientoj kaj elektitaj reprezentantoj;
- konservu kapablolimojn kaj domajn-precizajn teoremnomojn;
- registru nefinitajn asertojn en `CONJECTURES.md`;
- auditu ĉefajn deklarojn en AxiomChecks kaj `AXIOMS.md`.

## Dokumentoj kaj kontrolo

Spegulu paĝojn laŭ la sama vojo en kvar lingvoj kaj sinkronigu publikajn
ŝanĝojn. Post aksiomaj ŝanĝoj rulu `./scripts/sync-doc-reference-tables.sh`.
La deviga `./scripts/quality-gate.sh` kontrolas dokumentojn, radikajn importojn,
plenan konstruon, lint, ekzemplojn kaj aksiomojn.

## PR-listo

- [ ] unu celo kaj klara restanta limo;
- [ ] fokusita kaj plena konstruoj sukcesas;
- [ ] ĉefaj supozoj kaj ruleblaj ŝanĝoj estas audititaj;
- [ ] arkitekturo, stato, referencoj kaj lingvoj estas aktualaj;
- [ ] neniuj nerilataj, generitaj, sekretaj aŭ privataj dosieroj.

Revizio kontrolas ankaŭ la teoreman aserton kaj modelan intencon. Vidu
[Regadon](GOVERNANCE.md).
