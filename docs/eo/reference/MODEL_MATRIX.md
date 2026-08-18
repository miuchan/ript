# Matrico de modelkapabloj

[English](../../en/reference/MODEL_MATRIX.md) · [简体中文](../../zh-CN/reference/MODEL_MATRIX.md) ·
[日本語](../../ja/reference/MODEL_MATRIX.md) · [Esperanto](MODEL_MATRIX.md)

Nur realigitaj kaj kompilitaj kapabloj estas markitaj kiel subtenataj. La
maŝine kontrolata kanona matrico estas
[`MODEL_MATRIX.md`](../../../MODEL_MATRIX.md).

## Proceza strukturo

| Modelo | Seria | Tensora | Forĵeto | Kopio |
| --- | --- | --- | --- | --- |
| `FiniteFunction` (nula kosto) | Jes | Jes | Jes | Jes |
| `FiniteFunction.Metered` | Jes | Ne | Ne | Ne |
| Seria termmodelo | Jes | Ne | Ne | Ne |
| Simetria monoida termmodelo | Jes | Jes | Ne | Ne |
| `FiniteStochastic` (ekzakta `ℚ≥0`) | Jes | Jes | Jes | Jes |
| Fini-distribua Kleisli | Jes | Ne | Ne | Ne |
| Mathlib `Stoch`-ponto | Jes | Jes | Per `Stoch` | Per `Stoch` |
| Ekzakta finia decida tavolo | Per `FinStoch` | Ne | Ne | Ne |
| Totala komputado (`Fin 4 → Nat`) | Jes | Dufunktoro | Ne | Ne |
| Parta komputado (`Option` Kleisli) | Jes | Dufunktoro | Ne | Ne |
| Finia kaŭza DAG | Topologia generado | Per `FinStoch`-statoj | Ne | Ne |
| Finiaj termikaj sistemoj | Gibbs-konserva kategorio; fermaj kaj ban-helpataj protokoloj | Dufunktoro; samtemperatura Gibbs-tensoro | Neniu eksportita termika forĵeto | Ne |
| Finiaj kvantumaj Kraus-kanaloj | Kraus-kategorio | Jes | Jes | Ne |
| Klasika kvantuma senfaziga subkategorio | Jes; identeco estas senfazigo | Dufunktoro | Per ĉirkaŭa spura forĵeto | Neniu eksportita kopio |

## Semantikaj kapabloj

| Modelo | Konveksa | Kaŭza | Decida | Termika |
| --- | --- | --- | --- | --- |
| `FiniteFunction` | Ne | Jes | Ne | Ne |
| `FiniteFunction.Metered` | Ne | Ne | Ne | Ne |
| Seria termmodelo | Ne | Ne | Ne | Ne |
| Simetria monoida termmodelo | Ne | Ne | Ne | Ne |
| `FiniteStochastic` | Jes | Jes | Ne | Ne |
| Fini-distribua Kleisli | Ne | Ne | Ne | Ne |
| Mathlib `Stoch`-ponto | Ne | Per `Stoch` | Per Mathlib Bayes-riskoj | Ne |
| Ekzakta finia decida tavolo | Ne | Per `FinStoch` | Antaŭa datenprilaboro, determinisma kaj plena finia Blackwell–Sherman–Stein inverso, racionala garbling-simplekso kaj apartigaj atestiloj | Ne |
| Totala komputado | Ne | Ne | Ne | Ne |
| Parta komputado | Ne | Ne | Ne | Ne |
| Finia kaŭza DAG | Neniu ĝenerala interfaco | Jes | Ne | Ne |
| Finiaj termikaj sistemoj | Neniu ĝenerala interfaco | Per `FinStoch` | Ne | Racionaleca klasifiko, neracionala kontraŭekzemplo, fermprotokola maleblo, KL/libera energio/korelacio/Landauer-limoj |
| Finiaj kvantumaj Kraus-kanaloj | Ne | Jes | Ne | Ne |
| Klasika kvantuma senfaziga subkategorio | Neniu ĝenerala interfaco | Jes | Ne | Ne |

## Komputebleco

| Modelo | Stato |
| --- | --- |
| `FiniteFunction` kaj `Metered` | Ruleblaj |
| Seria kaj simetria monoida termmodeloj | Pruva tavolo |
| `FiniteStochastic` kaj finia Kleisli | Ruleblaj |
| Mathlib `Stoch`-ponto | Semantika tavolo |
| Ekzakta finia decida tavolo | Ekzaktaj minimumoj, racionala konveksa reflektado, strikta apartigo, fibraj atestantoj kaj stokasta `1/4 < 1/2`-atestilo kompiliĝas |
| Totala/parta komputado kaj finia kaŭza DAG | Ruleblaj |
| Finiaj termikaj sistemoj | Ekzaktaj statoj, kanaloj, spuroj, marĝenoj, racionalaj pezoj kaj bateriaj atestantoj estas ruleblaj; reela analizo restas pruva |
| Finiaj kvantumaj Kraus-kanaloj | Matrica pruva tavolo; bazaj etikedoj ruleblaj |
| Klasika kvantuma senfaziga subkategorio | Ekzakta `FinStoch`-fonto; nekomputebla kompleksa matrica semantiko |

## Gravaj limoj

- Kvantuma “forĵeto” estas la spura kanalo kaj “kaŭza” signifas `eq_discard` kaj `comp_discard`; klasika kopio ne estas konkludata.
- `Metered` restas seria ĉar pruv-rilataj kostoj distingas egalajn funkciojn kun malsamaj unuoj.
- La plena finia Blackwell-inverso bezonas ne-malplenan kaŝan stataron; kompilita malplena kontraŭekzemplo pruvas la neceson.
- La termika modelo apartigas ekzaktajn racionalajn operaciojn de reela analizo; mekanika laboro bezonas eksplicitan entropi-neŭtralan baterion.
- La klasika kvantuma identeco estas senfazigo, ne la plena Kraus-identeco.

## Komuna ses-modela sintaksa tranĉo

La unu-kosta seria signaturo en `Ript.Examples.CommonBitRealizations` estas
unu efektiva sintakso interpretita en ĉiuj ses modelfamilioj. Ĝi konservas la
indiĝenan komputan rimedon kaj eksplicitigas la aliajn nunajn abstraktajn
kostkontraktojn kaj modelspecifajn pruvdevojn.

| Modelfamilio | Konkreta realigo | Indiĝena rimedinterpreto | Kontrolita observado |
| --- | --- | --- | --- |
| Klasika probablo | Ekzakta determinisma `FinStoch`-negacio | `Nat`; nula kanalkosto limigita de unu | Negita eliro havas probablon unu |
| Kvantuma procezo | Pauli-X Kraus-kanalo | `Nat`; nula abstrakta kanalkosto limigita de unu | Baza denseco `|b><b|` iras al `|¬b><¬b|` |
| Kaŭza modelo | Neganta infana mekanismo en finia dunoda DAG | `Nat`; nula stokasta kosto limigita de unu | La infano estas la negacio de la gepatro kun probablo unu |
| Komputado | Totala Bulea pordo | `ComputationResource`; unu unuo iĝas unu paŝo kaj unu pordo | La rezulto estas negacio kaj la tradukita kosto estas ekzakta |
| Semantika informo | Inverse reetikedita Bulea eksperimento | `Nat`; nula kanalkosto limigita de unu | Blackwell-ekvivalenta al perfekta observado; divenvaloro estas `1/2` |
| Termodinamiko | Gibbs-konserva turno de la degenerita termika bito | `Nat`; nula abstrakta kosto limigita de unu | La ekzakta kanalo turnas la biton kaj konservas ekvilibron |

`sixModelFlipAgreement` pakas la ses faktojn en unu kerne kontrolitan
propozicion. Ĝi estas netriviala komuna tranĉo, sed ankoraŭ ne reprezenta aŭ
kompleteca teoremo por la plenaj ses modelfamilioj.

## Rimedreprezentoj kaj pli alta organizado

Kost-induktitaj kaj atingitaj buĝetfiltradoj havas seriajn/tensorajn leĝojn kaj
ekzaktajn ir-revenajn teoremojn. `ProcessModel R` formas fiks-rimedajn fibrojn;
`ResourceModel` formas la objektojn de la totala bikategorio. Heterogena 1-ĉelo
portas `φ : R →+o S`; identecoj, komponado, flankkomponado, interŝanĝo,
asociiloj, unuigiloj, kvinangulo kaj triangulo estas pruvitaj. La ordinara
homotopia lokalizado estas preta; plena pli alta lokalizado, kiu retenas
neinverseblajn 2-ĉelojn, restas malferma.

Komuna monoida sintakso povas puŝi kostojn laŭ `φ` sen ŝanĝi dratojn aŭ
generatorojn. La esprimtraduko estas inversebla, la reprezento de heterogenaj
interpretoj estas ekzakta, kaj la libera modelo ekzakte realigas la tradukitan
buĝeton.

## Interna univalenta tavolo

Ĝi enhavas interfackodojn, strukturajn ekvivalentojn, internajn identecojn,
grupoidon, profundajn procezojn, objektan kompletigon, skeleton,
antaŭgarbojn/Yoneda, simplician nervon kaj Rezk-klasikan diagramon. Ĝi ne
aldonas eksteran `Equiv α β → α = β` kaj ne pretendas kompletan Rezk- aŭ
bikategorian lokalizadon de la totala modelbikategorio.
