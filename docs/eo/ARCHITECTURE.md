# Arkitekturo

[English](../en/ARCHITECTURE.md) · [简体中文](../zh-CN/ARCHITECTURE.md) ·
[日本語](../ja/ARCHITECTURE.md) · [Esperanto](ARCHITECTURE.md)

Ript estas organizita tiel, ke ruleblaj finiaj modeloj ne dependas de
kvocientoj, mezurteorio, pli alta kategori-teorio aŭ interna univalenteco.
Ĉiu tavolo rajtas uzi la interfacojn sub ĝi; inversaj importoj estas intence
malpermesitaj per revizio kaj la radika modulstrukturo.

## Direkto de dependecoj

```text
Rimeda algebro
      ↓
Interfacoj de kostitaj procezoj
      ↓
Rimeda reindeksado kaj heterogenaj modelmapoj
      ↓
Rulebla sintakso ──→ Semantiko kaj termmodeloj
      ↓                       ↓
Finiaj modeloj ───────→ Ĝeneralaj semantikaj pontoj
      ↓                       ↓
Modela bikategorio kaj lokalizado
      ↓
Interna univalenta interpreto
```

La lasta tavolo interpretas profundan sintakson. Ĝi ne ŝanĝas egalecon de Lean
kaj ne aldonas univalentecon al la supraj tavoloj.

## Kerno de rimedoj kaj procezoj

`Ript/Resource/` difinas la algebron por mezuri procezojn:

- ordigitaj adiciaj rimedoj;
- buĝetoj kaj buĝetitaj morfismoj;
- monotona transporto kaj ordigita adicia ŝanĝo de rimeda algebro;
- kost-induktitaj kaj atingitaj filtradoj;
- leĝoj pri paralelaj buĝetoj.

`Ript/Core/` ligas tiun algebron al kategorioj kaj kapabloj:

- proceza kosto kaj seria subadicio;
- laŭvolaj paralela kosto, struktura kosto, konvekseco, kopio kaj forĵeto;
- simuladoj kaj monotonaj mapoj;
- kapablaj interfacoj, kiuj ne konkludas aldonan strukturon.

Tensoro ne implicas kopiadon aŭ forĵeton. Konvekseco, kaŭzeco kaj termika
strukturo estas same eksplicitaj kapabloj, ne tutmondaj defaŭltoj.

## Sintakso kaj semantiko

`Ript/Syntax/` enhavas krudan tipitan sintakson, kostokalkulon kaj eksplicitajn
derivojn. La kruda sintakso restas rulebla.

`Ript/Semantics/` enhavas:

- interpretojn en kostitajn kategoriojn;
- taksadon kaj kostan validecon;
- ekvacian validecon;
- kvocientajn termmodelojn kaj relativan kompletecon;
- simetrian monoidan semantikon kaj komencecon;
- komun-sintaksajn interpretojn tra ordigitaj adiciaj rimedŝanĝoj, kun
  inversebla esprimtraduko kaj ekzakta kompleteco de la kost-puŝita libera modelo.

Kvocientoj restas en la pruva tavolo. Uzanto, kiu nur taksas finian sintakson,
ne devas plenumi kvocientan maŝinaron.

## Konkretaj modeloj

`Ript/Models/` kaj ĝiaj subdosierujoj realigas semantikajn ekzemplerojn:

- `FiniteFunction`: determinisma bazo kaj eksplicita kartezia kopio/forĵeto;
- `FiniteStochastic`: normaligitaj ekzaktaj racionalaj kanaloj, komponado,
  tensoro, konveksaj miksaĵoj, kopio kaj forĵeto;
- `FiniteDistribution`: finia distribua monado kaj Kleisli-reprezento;
- probablaj moduloj: ponto al Mathlib `Stoch`;
- decidaj moduloj: Blackwell-komparo, ekzakta risko, rimedlimoj kaj atestiloj;
- komputaj moduloj: formalaj paŝoj/demandoj/memoro/pordoj, ne murhora tempo; hazardigita komputado parigas ekzaktajn finiajn kernojn kun la sama kvar-rimeda algebro;
- kaŭzaj moduloj: finiaj topologie ordigitaj DAG-oj kaj malmolaj intervenoj;
- termikaj moduloj: disigo de ekzaktaj kanaloj kaj realvalora analizo;
- kvantumaj moduloj: sur la plena simetria monoida Kraus-kategorio estas instrumentoj, rezult-regata retrokuplo kaj dependa bind; `InstrumentTree` estas la indukta normforma kaj komputebla-buĝeta tavolo.
- `NoisyBitRealizations` estas la unua ses-modela komuna brua sintakso, inkluzive koher-konservan hazard-unuecan kvantumon kaj hazardigitan komputadon.
- `Syntax.Branching` komputas fiksprofundajn adaptajn duumajn historiojn, pozitivajn branĉtabelajn normformojn, ekzaktajn vojkostojn, plejmalbon-okazajn buĝetojn, registritan stokastan reprezenton kaj observan kompletecon; `AdaptiveNoiseRealizations` donas ses indiĝenajn modelrealigojn.
- `Syntax.DependentBranching` ĝeneraligas al vari-profundaj generator-dependaj finiaj rezultoj, eksplicitaj historiaj ekvivalentoj kaj konservema duuma enmeto; `Examples.DependentBranching` estas la rulebla heterogen-rezulta atestanto.
- `Syntax.DependentBranching.Free` organizas branĉalgebrojn kiel kategorion, pruvas komencan arbalgebron, ekvacian validecon/kompletecon kaj serian greftan monoidon, kaj reprezentas alton/buĝeton per nombraj fold-oj.
- `Syntax.DependentBranching.Monoidal` donas al la modelalgebra kategorio elektitajn finiajn produktojn, kartezian simetrian monoidan koheron, komponantan produkt-fold-reprezenton kaj komunan modelan kompletecon.
- `Syntax.DependentBranching.Parallel` pakas eksplicitajn heterogenajn lenojn, ekzaktan sendependan stokastan faktoradon, lenan simetrion, rimedadicion, komun-fazan greftadon kaj striktan tensor–serian interŝanĝon.

La [matrico de modelkapabloj](reference/MODEL_MATRIX.md) estas la aŭtoritata
registro de laŭvolaj strukturoj.

## Pli alta organizado

`Ript/Higher/` kunigas procezmodelojn en bikategorion:

- 0-ĉeloj estas rimed-indeksitaj simetriaj monoidaj procezmodeloj;
- 1-ĉeloj estas rimed-nepligrandigaj fortaj plektitaj monoidaj funktoroj;
- 2-ĉeloj estas monoidaj naturaj transformoj.

La fiks-rimeda bikategorio estas unu fibro de pli vasta kompilita tavolo.
`ResourceChangeModelHom` ligas `R`-modelon al `S`-modelo super ordigita adicia
mapo `R →+o S`. `ResourceModel`, `ResourceModelHom` kaj
`ResourceModelTransformation` kunigas respektive objektojn, 1-ĉelojn kaj
2-ĉelojn. Ili formas totalan bikategorion kun heterogena flankkomponado,
horizontala kaj vertikala komponado, interŝanĝo, asociiloj, unuigiloj,
kvinangulo kaj triangulo.

Bikategoria ekvivalento sola ne implicas nombran kostegalecon;
`CostExactModelEquivalence` registras la reflektadon eksplicite.

Lokalizado estas dividita laŭ forto:

- ordinara Gabriel–Zisman-lokalizado de la modela homotopia kategorio;
- irantaj ekzemploj por testi veran aldonon de inversoj;
- aparta preciza predikato de la bikategoria universala eco;
- neniu anstataŭigo de nepruvita kohereco aŭ esenca surĵeteco per aksiomoj.

La nuna mapspaca stako havas tri eksplicitajn prezentojn: duumaj marked-
zigzag-vortoj kun kvocientaj 2-ĉeloj, sendependaj dekstre-asociaj linearaj
hammock-vicoj, kaj negrupoida generita hammock-vojaro kun plenumeblaj
refinement-oj kaj arbitraj aligned krudaj ĉeloj. Ĉiuj estas kategorie
ekvivalentaj al la faktaj lokaj hom-kategorioj de la lokaliza celo; la nervaj
komparoj havas eksplicitajn homotopiajn inversojn, kaj la generita komparo
strikte faktoriĝas tra la lineara. Finiĝanta administra redukto forigas unuojn
kaj nestadon, kunfandas apudajn movojn kaj nuligas refinement-inversojn dum ĝi
konservas kvocientan semantikon. Kruda critical-pair joinability, la plena
klasika arbitra-krada movaro kaj norma malfort-ekvivalenta pako restas malfermaj.

## Interna univalenta interpreto

`Ript/Univalent/` difinas profundajn interfackodojn, apartajn sintaksojn por
interna struktura ekvivalento kaj identeco, grupoida interpreto, 0-tranĉitajn
objektkvocientojn, 1-tranĉitajn skeletojn, reprezenteblajn antaŭgarbojn,
Yoneda-semantikon, simpliciajn nervojn kaj klasifikan diagramon.

Tio ne estas ekstera HoTT por Lean. Ript neniam postulas tutmondan mapon
`Equiv α β → α = β`; asertoj restas ĉe la interne interpretita sintakso kaj la
precizaj kompilitaj kategoriaj interfacoj.

## Ruleblaj kaj analizaj limoj

La finia kerno uzas ekzaktajn natur-nombrajn rimedvektorojn, finiajn tipojn,
nenegativajn racionalajn probablojn, decideblajn minimumojn kaj eksplicitajn
atestantojn. Reela analizo, mezurteorio, kvocientoj, elektitaj reprezentantoj
kaj matricaj pruvoj troviĝas en semantikaj tavoloj kaj povas esti nekomputeblaj.

## Publikaj statusregistroj

- `README.md`: konciza enirejo;
- `RESEARCH_STATUS.md`: homlegebla esplora resumo;
- `reference/MODEL_MATRIX.md`: kompilitaj modelkapabloj;
- `reference/BLUEPRINT.md`: dependecoj kaj teoremnivela stato;
- `reference/CONJECTURES.md`: nepruvitaj asertoj;
- `reference/AXIOMS.md`: realaj kernaj supozoj.
- `GOVERNANCE.md`: decida aŭtoritato kaj stabileca politiko;
- `SECURITY.md`: privata raportado kaj la subtenata fidolimo.

Se ili malkongruas, Lean-deklaroj kaj maŝine kontrolita audito superas. La sama
tirpeto devas rekunordigi la dokumentaron.

## Kvalita arkitekturo

`scripts/quality-gate.sh` spegulas CI kaj kontrolas pruvtruojn, proprajn
aksiomojn, fid-evitojn, nesekurajn deklarojn, tro larĝajn importojn, implicitajn
identigilojn, modulkovradon, senavertan konstruon, deklarajn kontrolojn,
ruleblajn ekzemplojn, la aksioman permesliston kaj Markdown-strukturon.
Vidu la [kontribuan gvidilon](CONTRIBUTING.md).
