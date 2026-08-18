# Formaliga plano de Ript

[English](../../en/reference/BLUEPRINT.md) · [简体中文](../../zh-CN/reference/BLUEPRINT.md) ·
[日本語](../../ja/reference/BLUEPRINT.md) · [Esperanto](BLUEPRINT.md)

La plano registras nur realigan staton kontrolitan de la Lean-kerno. La solaj
statusoj estas `DEFINED`, `STATEMENT_FORMALIZED`, `PROVED`, `BLOCKED` kaj
`OPEN_RESEARCH`. La [maŝina kanona plano](../../../BLUEPRINT.md) konservas la
plenan Lean-tipon, dependecojn, supozojn kaj fonton de ĉiu deklaro; ĉi tiu
traduko konservas la samajn fazlimojn kaj teoremfamiliojn.

## Esplorcelo

Konstrui komputeblan, maŝine kontroleblan, univalentan kaj pli-alt-kategorian
teorion de rimed-limigitaj informprocezoj, kun klasika probablo, kvantumaj
procezoj, kaŭzaj modeloj, komputado, semantika informo kaj termodinamiko kiel
malsamaj modeloj ligitaj per reprezentaj kaj kompletecaj teoremoj. Loka
`PROVED`-statuso ne signifas, ke la tuta celo estas finita.

## Ĉefa dependeca direkto

```text
Rimeda algebro → Kostita procezo → Buĝetoj/filtradoj/rimedŝanĝoj
      ↓
Seria sintakso → Interpreto → Valideco → Termmodelo → Relativa kompleteco
      ↓
Monoida sintakso → Paralela kosto → Semantiko → Libera komenceco
      ↓
Funkciaj / probablaj / decidaj / komputaj / kaŭzaj / termikaj / kvantumaj modeloj
      ↓
Modelbikategorio → Heterogena totala bikategorio → Lokalizado
      ↓
Interna univalenta sintakso → Grupoido/kvociento/skeleto → Yoneda → Nervo → Klasifika diagramo
```

Komuna monoida sintakso povas puŝi nur siajn kostojn laŭ `φ : R →+o S`.
Dratoj kaj generatoroj restas samaj, esprimtraduko estas inversebla, heterogena
interpreto ekvivalentas al ordinara puŝita interpreto, kaj la libera modelo
ekzakte realigas la tradukitan buĝeton.

## Fazaj statoj

| Fazo | Amplekso | Stato |
| --- | --- | --- |
| 0 | Medio, projekto, dokumentaro, CI kaj auditbazo | `PROVED` |
| 1 | Seria rimed-proceza vertikala tranĉo | `PROVED` |
| 1 (finia determinisma) | Kartezia tensoro, kopio/forĵeto, kaŭzeco, Bulea atesto | `PROVED` |
| 1 (reprezento) | Kostoj kaj atingitaj buĝetfiltradoj kun ekzaktaj revenoj | `PROVED` |
| 2 | Tensoro, simetrio, paralelaj rimedoj kaj libera universala levo | `PROVED` |
| 3–5 | Finia stokastiko, distribua Kleisli kaj Mathlib `Stoch`-reprezento | `PROVED` |
| 6 | Blackwell-ordo, finia risko, plena inverso, racionala apartigo, semantika valoro | `PROVED` |
| 7 (komputado) | Plurdimensia totala kaj `Option`-parta komputado | `PROVED` |
| 7 (kaŭza) | Finiaj DAG-oj, komunaj distribuoj, intervenoj kaj `FinStoch` | `PROVED` |
| 8 | Finiaj ekvilibroj, Gibbs-klasifiko, libera energio, korelacio, Landauer | `PROVED` |
| 9 | Finiaj Kraus-kanaloj kaj fidela klasika enigo | `PROVED` |
| 10 | Fiks-rimeda modelbikategorio, 2-ĉeloj, kohereco kaj kost-ekzakta ekvivalento | `PROVED` |
| 10 (heterogenaj rimedoj) | Reindeksado, heterogenaj fortaj modelmapoj kaj buĝettransporto | `PROVED` |
| 10 (heterogena sintakso) | Kostpuŝo, inverseblaj esprimoj, interpreto kaj tradukita kompleteco | `PROVED` |
| 10 (komuna ses-modela tranĉo) | Unu unu-kosta Bulea turno kun probabla, kvantuma, kaŭza, komputa, semantika kaj termika interpretoj | `PROVED` |
| 10 (totala bikategorio) | Pakitaj rimedalgebroj, heterogenaj 1-/2-ĉeloj, interŝanĝo, kvinangulo, triangulo | `PROVED` |
| 10 (ordinara lokalizado) | Kost-ekzakta lokalizado de la modela homotopia 1-kategorio | `PROVED` |
| 11 | Senaksioma profunda sintakso, kvocienta grupoido kaj interna univalenteco | `PROVED` |
| 12 (tranĉita/antaŭgarba/grupoida) | Objekta kompletigo, skeleto, Yoneda kaj ordinara lokalizado | `PROVED` |
| 12 (simplicia) | Kan, strikta Segal, kvazaŭkategorio, 2-koskeleto kaj homotopia reakiro | `PROVED` |
| 12 (klasifika diagramo) | Rezk-diagramo, ekstera Segal, kongruaj limoj kaj fibradoj | `PROVED` |
| 12 (pli alta lokaliza specifo) | Markinversigo, pseŭdofunktora antaŭkompono, lokaj ekvivalentoj, irantaj testoj | `PROVED` |
| 12 (pli alta lokaliza konstruo) | Lokaliza pseŭdofunktoro por la plena rimed-proceza bikategorio | `OPEN_RESEARCH` |

## Ĉefaj teoremfamilioj

- Rimedoj: buĝetitaj identecoj/komponado, filtrado-kostaj rondiroj kaj reindeksado.
- Sintakso: `eval_cost_le`, seria/monoida valideco, relativa kompleteco kaj unikeco de libera levo.
- Heterogena sintakso: reprezenta ekvivalento, tradukita taksa limo kaj ekzakta libera buĝeto.
- Ses modeloj: modelspecifaj Buleaj turnoj, komputa rimedtraduko kaj `sixModelFlipAgreement`.
- Probablo kaj decido: `FiniteStochastic`, Kleisli/`Stoch`, Blackwell-inverso kaj racionala apartigo.
- Komputado kaj kaŭzeco: plurdimensiaj limoj, parta komputado, DAG-normaligo kaj intervenoj.
- Termodinamiko: Gibbs-konservo, KL, libera energio, korelacio, Landauer kaj ban/bateriaj atestantoj.
- Kvantumo: Kraus-pozitiveco, spuro-konservo, tensoro, kompleta pozitiveco kaj klasika enigo.
- Pli altaj tavoloj: fiksaj kaj totalaj bikategorioj, kost-ekzaktaj ekvivalentoj kaj lokalizaj testoj.
- Univalenteco: interna identeco, objekta kompletigo, Yoneda, Kan-nervo, Segal kaj klasifika diagramo.

Por la ekzakta Lean-tipo kaj `Classical.choice`-limo de ĉiu deklaro, uzu la
[plenan anglan planon](../../en/reference/BLUEPRINT.md) aŭ la
[maŝinan kanonan registron](../../../BLUEPRINT.md).

## Nefinita limo

Restas nepruvitaj: konkretigo de la komuna sintakso en ĉiuj ses modelfamilioj;
modelspecifaj reprezentaj, konservemaj kaj kompletecaj teoremoj; veraj
intermodelaj komparoj; kaj universala interna-univalenta aŭ norma
complete-Segal-lokalizado de la plena rimed-proceza bikategorio. Neniu el tiuj
estas kaŝita kiel Lean-aksiomo aŭ pruvita lokokupilo.
