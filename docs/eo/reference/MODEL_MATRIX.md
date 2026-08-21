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
| Totala komputado (`Fin 4 → Nat`) | Jes | Simetria monoida; ekzakta rimedadicio | Ne | Ne |
| Parta komputado (`Option` Kleisli) | Jes | Dufunktoro | Ne | Ne |
| Finia kaŭza DAG | Topologia generado | Per `FinStoch`-statoj | Ne | Ne |
| Finiaj termikaj sistemoj | Gibbs-konserva kategorio; fermaj kaj ban-helpataj protokoloj | Simetriaj monoidaj produkt-ekvilibroj; samtemperatura Gibbs-tensoro | Neniu eksportita termika forĵeto | Ne |
| Finiaj kvantumaj Kraus-kanaloj | Kraus-kategorio | Plena simetria monoida strukturo kun inversebla baz-kohero | Jes | Ne |
| Klasika kvantuma senfaziga subkategorio | Jes; identeco estas senfazigo | Fidela simetria monoida mezur–prepara bildo; la plena subkategorio retenas dufunktoron | Per ĉirkaŭa spura forĵeto | Neniu eksportita kopio |

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
| Ekzakta finia decida tavolo | Ne | Per `FinStoch` | Antaŭa datenprilaboro, determinisma kaj plena finia Blackwell–Sherman–Stein inverso, racionala garbling-simplekso, apartigaj atestiloj kaj tut-taskaj semantikaj ordo/profila kompleteco | Ne |
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
| Totala/parta komputado kaj finia kaŭza DAG | Ruleblaj; last-write-wins kaj redunda-mekanisma forigo por fiks-DAG-aj molaj/stokastaj/malmolaj programoj ankaŭ ruleblas |
| Finiaj termikaj sistemoj | Ekzaktaj statoj, kanaloj, spuroj, marĝenoj, racionalaj pezoj kaj bateriaj atestantoj estas ruleblaj; reela analizo restas pruva |
| Finiaj kvantumaj Kraus-kanaloj | Matrica pruva tavolo; bazaj etikedoj, finiaj instrumentrezultoj kaj branĉa nombrado ruleblaj |
| Klasika kvantuma senfaziga subkategorio | Ekzakta `FinStoch`-fonto; nekomputebla kompleksa matrica semantiko |

## Gravaj limoj

- Kvantuma “forĵeto” estas la spura kanalo kaj “kaŭza” signifas `eq_discard` kaj `comp_discard`; la plena Kraus-kategorio havas pruvitajn naturecon, kvinangulon, triangulon, ambaŭ sesangulojn kaj simetrion, sed klasika kopio ne estas konkludata.
- `Metered` restas seria ĉar pruv-rilataj kostoj distingas egalajn funkciojn kun malsamaj unuoj.
- La plena finia Blackwell-inverso bezonas ne-malplenan kaŝan stataron; kompilita malplena kontraŭekzemplo pruvas la neceson.
- La termika modelo apartigas ekzaktajn racionalajn operaciojn de reela analizo; mekanika laboro bezonas eksplicitan entropi-neŭtralan baterion.
- La klasika kvantuma identeco estas senfazigo, ne la plena Kraus-identeco.

La finia kvantuma instrumenttavolo apartigas komplete pozitivajn operacibranĉojn
de ilia spuro-konserva sumo. Rezultprobabloj estas nenegativaj kaj sumiĝas al unu;
pozitivaj rezultoj havas postajn densecmatricojn; seria komponado registras parojn;
sendependaj tensoroj multiplikas probablojn. Ĉiu instrumento havas CPTP-reprezenton
al “klasika rezulto × resta sistemo”, kies diagonalaj blokoj reakiras la branĉojn.
La kohera plus-ekzemplo kaj unu-/du-unua `InstrumentSyntax` estas kontrolitaj.
Rezult-elektita Pauli-X-retrokuplo konservas la probablojn kaj korektas ambaŭ
postajn statojn kaj la rezult-forgesitan suman kanalon al `false`.
Dependa bind permesas rezult-dependajn sekvajn instrumentojn kaj rezulttipojn;
kunaj probabloj sekvas la Born-ĉenleĝon kaj nestitaj bind-oj asocias per
Sigma-arba reetikedado. La du-ronda tri-historia ekzemplo havas `1/2, 1/2, 0`.
`InstrumentTree` estas la unuaklasa indukta sintakso: dependaj historioj estas
kanonaj normformoj, taksitaj branĉoj estas ekzakte historiaj vojkomponaĵoj, kaj
ĉiu preciza historikosto estas limigita de komputebla arbobuĝeto.

La hazardigita komputmodelo parigas ruleblan ekzaktan `FinStoch`-kernon kun
kvar-dimensia `ComputationResource`; serio/tensoro ekzakte adicias, kohermapoj
estas nulkostaj kaj buĝetkontrolo estas rulebla kaj valida.

## Ses-modela ekzakta brua tranĉo

`NoisyBitRealizations` interpretas la saman `3/4–1/4` BSC-on kiel probablon,
plus-koheron konservantan hazard-unuecan kvantumon, bruan kaŭzan mekanismon,
kvar-rimedan hazardigitan programon, semantikan eksperimenton kaj
Gibbs-konservan procezon. Kvantumo estas distingita de mezur–preparo;
semantikaj risko kaj valoro estas ambaŭ `1/4`, kaj paralelaj komputrimedoj
ekzakte duobliĝas.

## Ses-modela adapta branĉarba tranĉo

`Syntax.Branching` komputas kompletajn historiojn, pozitivajn racionalajn
branĉtabelajn normformojn, ekzaktajn vojkostojn kaj plejmalbon-okazan buĝeton
por arbitraj fiksprofundaj duumaj adaptaj arboj, kaj pruvas fidelecon de la
registrita `FinStoch`-reprezento kaj observan kompletecon.
`AdaptiveNoiseRealizations` donas kvar ekzaktajn branĉojn kaj realigojn kiel
probablo, kohera hazard-unueca instrumentarbo aparta de mezur–preparo, kvar-noda
kaŭza DAG, hazardigita programo kun rimedo `(3,3,2,3)`, nul-riska semantika
eksperimento kun valoro `1/2`, kaj Gibbs-konserva termika procezo. Kompleteco
ankaŭ distingas ĝin de fiksa du-kvaron-turna arbo.

## Vari-profundaj dependaj finiaj branĉoj

`DependentBranching` permesas malsaman arbitran finian rezulttipon por ĉiu
generatoro kaj arbitran daŭrigarbon por ĉiu rezulto. Dependaj Sigma-historioj,
enumerado, decidebla egaleco, alto, ekzaktaj vojkostoj kaj finia-supremuma
plejmalbona buĝeto estas ruleblaj. Pozitiva racionala semantiko havas
registritan-tabelan reprezenton kaj observan kompletecon laŭ eksplicitaj
historiaj ekvivalentoj. La duuma enmeto konservas probablon, staton, koston kaj
kanalerojn. `Bool`/`Fin 3`-ekzemplo havas kvin historiojn de longoj unu ĝis tri,
alton `3`, buĝeton `4`, kaj masojn `1/2, 1/6, 1/6, 1/12, 1/12`.
`DependentBranching.Free` nun donas kategorion de branĉalgebroj, komencan
arbalgebron, unikan fold, absolute kompletan kongruecon kaj asocian unuhavan
serian foligreftadon. Alto kaj buĝeto estas kanonaj fold-oj kaj subadiciaj;
la ekzemplo kalkulas folnombron `5`, alton `6`, buĝeton `8`.
`DependentBranching.Monoidal` plue donas kartezian simetrian monoidan
modelalgebran strukturon, ekzaktan produkt-fold kaj komunan kompletecon.
`ParallelProtocol` kaj `LaneProtocol` donas duumajn kaj arbitrajn finiajn
n-umajn sendependajn lenojn, ekzaktan stokastan faktoradon, rimedadicion,
reindeksan koheron kaj striktan tensor–serian interŝanĝon. Ses-modelaj realigoj
de ĉiu finia pozitiva dependa normalformo kaj egalreflekto ankaŭ kompiliĝas;
ekstere specifita kongrua cel-ekvilibro havas unikan termikan levon.

Ĉe la ekzakta finia semantika nombrovalora tavolo, universala nenegativa
taskvaloro ekvivalentas al Blackwell-domino, kaj la tut-taska valorprofilo
rilate al la kanona seninforma eksperimento klasifikas Blackwell-ekvivalentecon.
Bulea kontraŭekzemplo montras ke unu taska skalaro ne estas kompleta;
rimed-limigitaj profiloj kaj pli riĉaj/senfinaj tasklingvoj restas malfermaj.

La interna bildo de la Gibbs-konserva forgesa mapo estas ekzakte la stokastaj
kanaloj kiuj puŝas la specifitan font-ekvilibron al la specifita cel-ekvilibro,
kaj ĉiu kongrua kanalo havas unikan termikan levon. Pli striktaj
energi-konservaj sistem–banaj unuecaj dilatbildoj restas malfermaj.

Fiks-DAG-aj kaŭzaj intervenoj subtenas arbitrajn gepatro-asign-dependajn molajn
mekanism-anstataŭigojn, kun stokastaj kaj Dirac-malmolaj kazoj kiel specialaĵoj.
Finiaj programoj normaliĝas al reduktita last-write-wins formo, ekzakte
reprezentas la finan modelon kaj komunan statkanalon, kaj estas kompletaj por
loka mekanisma semantiko. Heterogenaj portantoj, grafŝanĝo kaj politik-dependaj
intervenoj restas malfermaj.

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

`CompositionalBitRealizations` etendas la komunan limon al du tipitaj stadioj.
Probablo uzas Chapman–Kolmogorov-komponadon; kvantumo aplikas Pauli-X dufoje;
kaŭzeco uzas du negantajn mekanismojn de normaligita trinoda ĉeno; komputado
registras du paŝojn kaj du pordojn; semantika posttraktado reakiras perfektan
observadon kun valoro `1/2`; kaj du liberaj termikaj turnoj formas identecan
ferman protokolon. `sixModelCompositionAgreement` pakas la rezultojn. Branĉado,
ĝenerala bruo kaj ĝeneralaj mezurinstrumentoj restas ekster ĉi tiu inversebla
tranĉo.

La lineara kompona teorio nun ankaŭ havas ekzaktajn reprezenton kaj
kompletecon. `normalize` kalkulas la unikan normvojon de ĉiu tipita esprimo;
`derives_unique` pruvas formalajn egalojn ĉe fiksaj finpunktoj;
`inImage_iff_eq_canonical` karakterizas ĉiun hom-bildon kiel unu-elementan;
kaj `sixModelSemanticCompleteness` pruvas egalreflektadon por ĉiuj ses modeloj.
Tio dependas de la maldikeco de la nuna lineara grafeo kaj ne estas etendita al
la pli riĉa operacia lingvo sube.

`OperationalErasureRealizations` aldonas la unuan karakterizan
neinversigeblan operacion. La komuna rimedo aparte registras malkovron kaj
viŝadon kaj ekzakte mapas ilin al unu komputa demando kaj unu pordo. Probablo
uzas konstantan `false`-kanalon; kvantumo uzas mezur–preparan reset-on; kaŭzeco
pruvas mekanism-anstataŭigon per `do(effect=false)`; semantika valoro falas de
`1/2` al nulo; termodinamiko uzas memor–labor-baterian sistemon kaj saturas la
Landauer-laboregalon anstataŭ postuli senpagan viŝadon. La paka teoremo estas
`sixModelErasureAgreement`.

## Ses-modela paralela tranĉo

La sama `flip ⊗ flip` simetria monoida esprimo en
`ParallelBitRealizations` sendepende turnas ambaŭ bitojn en probablo, la plena
finia Kraus-kategorio, du kaŭzaj mekanismoj, ekzakta kvar-koordinata
komputado, semantikaj eksperimentoj kaj Gibbs-konserva termodinamiko. La
kvantuma branĉo aplikas tensorajn Pauli-X-kanalojn komponente al arbitraj
produktaj densecmatricoj. Monoida pruvtraduko estas konservema; ĉiu
heterogena interpreto havas rektan fortan
simetrian rimedŝanĝan liberan levon kun kuntirebla strikta etenda tipo.
`ParallelBitHigherModels` poste pakas la komunan liberan sintakson kaj la ses
celojn, inkluzive la plenan Kraus-procezmodelon, kiel objektojn de la totala rimed-modela bikategorio. La ses levoj
fariĝas fortaj plektitaj 1-ĉeloj kun kontrolitaj rimedmapoj; la komputa 1-ĉelo
retenas la ekzaktan kvar-koordinatan paralelan koston.

## Nemaldika diamanta reprezento kaj kompleteco

La reuzebla fundamento nun estas ĝenerala. `SequentialNormalForm` reprezentas
esprimojn de ajna tipita seria signaturo per generatoraj vojoj, pruvas
deriveblon iff vojegalon, donas eksplicitan kategorian ekvivalenton inter la
kvocienta termmodelo kaj tipitaj vojoj kun ekzakta kostkonservo, identigas la semantikan bildon de ĉiu
heterogena interpreto kun ĝia vojbildo, kaj pruvas ĉiun vojfidelan interpreton
kompleta. `SequentialFree` kaj `ResourceChangingSequentialFree` donas
kuntireblajn strikt-etendajn tipojn, generatoran kongruon kaj tradukitajn kostlimojn. Ili
postulas nek finiecon, neciklecon nek maldikecon.

`DiamondBitTheory` kunigas la inverseblan kaj viŝan branĉojn en libera
kategorio kun du paralelaj enir–eliraj vojoj. Sendependaj rimedkoordinatoj
pruvas ilian formalan malegalecon. Branĉ-konserva normaligo donas ekzaktan
dek-vojan normreprezenton, ekzaktan du-elementan enir–eliran bildon kaj la
kompletecan kriterion “voja apartigo implicas egalreflektadon”.
`DiamondBitRealizations` kontrolas apartigon per ses modelspecifaj atestoj;
tial ĉiuj ses interpretoj estas kompletaj por ĉi tiu nemaldika teorio. La samaj
ses interpretoj ankaŭ induktas kanonajn rimedŝanĝajn funktorojn el unu libera
diamanta termmodelo, kun generatora kongruo kaj tradukitaj kostlimoj por ĉiu
libera morfismo.

## Rimedreprezentoj kaj pli alta organizado

Kost-induktitaj kaj atingitaj buĝetfiltradoj havas seriajn/tensorajn leĝojn kaj
ekzaktajn ir-revenajn teoremojn. `ProcessModel R` formas fiks-rimedajn fibrojn;
`ResourceModel` formas la objektojn de la totala bikategorio. Heterogena 1-ĉelo
portas `φ : R →+o S`; identecoj, komponado, flankkomponado, interŝanĝo,
asociiloj, unuigiloj, kvinangulo kaj triangulo estas pruvitaj. La ordinara
homotopia lokalizado estas preta. La totala modelbikategorio havas ankaŭ
Kan-an striktan-Segal objektkernon kaj plenajn lokajn mapnervojn, kun ekzakta
interna-ekvivalentklasa/identeca-eĝa korespondo, vertikalaj 2-simplaĵoj,
horizontal-komponaj simpliciaj mapoj kaj retenitaj neinversigeblaj 2-ĉeloj.
Plena pli alta lokalizado restas malferma.
La tutmonda Duskin 3-skeleto jam kompiliĝas: trianguloj retenas arbitrajn
kompon-komparajn 2-ĉelojn, kaj kvaredra limo havas unikan 3-simplaĵan plenigon
precize kiam la asociile korektita ekvacio validas. Tiuj datumoj etendiĝas al
tutdimensia koordinata duonsimplicia Duskin-nervo. Indiĝena plena Duskin-nervo
uzas strikte unuigajn malstriktajn fin-ordinalajn diagramojn kiel simplaĵojn;
ĉiu monotona mapo unuforme donas facon aŭ degeneron, la unua degenero kreas
identecan eĝon, kaj natura malkodigo celas la koordinatan duonsimplician nervon.
La dimensio-laŭa koordinata ekvivalento kaj plena complete-Segal 2-spaca
kunmeto restas malfermaj.

Komuna monoida sintakso povas puŝi kostojn laŭ `φ` sen ŝanĝi dratojn aŭ
generatorojn. La esprimtraduko estas inversebla, la reprezento de heterogenaj
interpretoj estas ekzakta, la pruvtraduko estas konservema, kaj rekta forta
simetria libera levo el la originala termmodelo ekzakte realigas la tradukitan buĝeton.

Komuna seria sintakso havas ankaŭ striktan komencecon: ordinara interpreto
unike etendiĝas al rimed-nepligrandiga funktoro, heterogena interpreto unike
etendiĝas laŭ `φ`, kaj ambaŭ etendaj tipoj estas kuntireblaj. La termmodelo estas
eksplicite ekvivalenta al la generatora vojkategorio kun ekzakta kostkonservo.
Tutmonde, ordinaraj interpretoj ekvivalentas al liber-fontaj rimed-monotonaj
funktoroj, kaj heterogenaj interpretoj al liber-fontaj rimedŝanĝaj funktoroj kun la fiksita `φ`.

## Interna univalenta tavolo

Ĝi enhavas interfackodojn, strukturajn ekvivalentojn, internajn identecojn,
grupoidon, profundajn procezojn, objektan kompletigon, skeleton,
antaŭgarbojn/Yoneda, simplician nervon kaj Rezk-klasikan diagramon. La
total-modela objektkerno, lokaj mapnervoj, koordinata duonsimplicia kaj
indiĝena plena Duskin-nervoj estas nova pli alta ponto. Ĝi ne aldonas eksteran
`Equiv α β → α = β` kaj ne pretendas jam kompletan complete-Segal-kunmeton
aŭ bikategorian lokalizadon de la totala modelbikategorio.
