# CX-I1 — Primer incremento del fundamento causal de intercambios

Fecha: 2026-09-28.
Rama: CausalGeometry/main.
Base: 9f52914ca4adfdb417777589eaa00e0c086a2b3d.
Código y verificador: 4004720716de078c2f82d61f8627b9c595081a8e.
Estado: SOURCE-WRITTEN / NON-KERNEL-PASS / LEAN-TYPECHECK-PENDING.
Nuevas filas acreditadas: 0.

## 1. Qué se ha implementado

Esta entrega empieza la fuente autónoma de CX y construye los prerrequisitos
que estaban alojados en la capa variacional. No modifica EventSystem,
CausalNumber, los pins de Lean/mathlib, las otras ramas ni GenContinuum.
No añade workflows. La realización ECIA permanece como frente separado.

Siete módulos nuevos están importados por la raíz:

- History/Composition.lean: productor histórico CausalPath.comp trasladado
  sin duplicación, junto con sus lemas; nuevas pruebas por inducción de unidad
  derecha y asociatividad.
- History/DiamondPaths.lean: los dos caminos reales de un diamante concurrente
  y sus lemas de longitud. Los nombres históricos en CausalVariational se
  conservan, aunque ya no exigen una estructura variacional para construirse.
- History/EventList.lean: observación de ocurrencias ordenadas, compatibilidad
  con composición/casts y extensionalidad de caminos con extremos fijos.
- Exchange/Basic.lean: pasos en Type con pivote, eventos, diamante admitido,
  prefijo y continuación; la posición se deriva de la longitud del prefijo.
  Se construyen los dos contextos y se prueban conservación de longitud,
  cota de posición, ausencia de conflicto y distinción de ocurrencias.
- Exchange/Path.lean: rutas mediante Quiver.Path y categoría mediante Paths
  nativos. El intérprete y su unicidad consumen Paths.lift/lift_unique del
  mathlib fijado; los contextos se extienden a funtores sobre rutas.
- Exchange/Variational.lean: la diferencia de acción contextual coincide con
  el defecto del diamante; Euler–Lagrange implica conservación de acción a
  lo largo de cualquier ruta de intercambios.
- Models/ExchangeThreeEvents.lean: seis historias y dos rutas ternarias sobre
  tres eventos causales reales, con observador separador y control del mismo tipo.

La categoría de intercambios es LIBRE en este incremento. No se han impuesto
relaciones de Yang–Baxter, inversos o identificación de rutas por extremos.
Tampoco se reclama que todos los intercambios generales sean cronológicos:
este es el primer dominio concreto del programa más amplio.

## 2. Conservación de productores anteriores

DiscreteAction.lean pasa a importar History.Composition; se ha trasladado
literalmente su bloque de composición, manteniendo sus nombres y firmas.
El resto de su fuente es idéntico al de la base.

ElementaryEulerLagrange.lean consume History.DiamondPaths. Los cuatro
productores trasladados conservan literalmente sus declaraciones. Hay una
única reparación adicional del cuerpo de actionDifference_diamondPaths:
tras pathAction_castEnd, se simplifican explícitamente pathAction_step,
pathAction_nil y add_zero en vez de terminar por rfl con términos +0 en un
grupo abstracto. El enunciado no cambia. Es una reparación por inspección
estática; no se atribuye a una ejecución de Lean que no se ha realizado.

Los tests reconstruyen las dos fuentes antiguas y contrastan sus hashes de
blob Git, invirtiendo únicamente los traslados y esa reparación declarada.
También reconstruyen exactamente la raíz anterior: solo se añaden los siete
imports al final. No se elimina ningún consumidor histórico.

## 3. Primer resultado: mismas historias extremas, rutas diferentes

El modelo usa EventSystem (Fin 3) Unit con causalidad y conflicto vacíos.
Las ocurrencias son distintas aunque todas sus etiquetas sean Unit. Se
construyen los caminos existentes CausalPath, no un portador sustituto de listas.

Las rutas son:

    route121: 012 -> 102 -> 120 -> 210
    route212: 012 -> 021 -> 201 -> 210.

Cada flecha procede de un diamante y sus contextos. Las posiciones derivadas
son respectivamente [0,1,0] y [1,0,1]. La fuente libre conserva su diferencia.
La observación eventList refleja igualdad de CAMINOS con extremos fijos;
no se utiliza para colapsar RUTAS entre esos caminos.

El intérprete al tipo ZMod 5 asigna a posición par m -> -m y a posición impar
m -> t-m. La memoria vive exclusivamente en la realización.

Se escriben pruebas de las fórmulas para todos los t,m:

    observe(t,route121,m) = -t-m
    observe(t,route212,m) = 2t-m.

Para t=2,m=0 se obtienen 3 y 4. Para t=0, el observador del mismo tipo
identifica ambas rutas para todo m. Cada acción elemental es involutiva.
Esto NO impone inversos en la categoría fuente ni construye aún un cociente twin.
No se reclama fidelidad global del modelo finito.

## 4. Segundo resultado: consumidor variacional intrínseco

Para un intercambio s:p->q con diamante d y cualquier Lagrangiano L, la
cancelación de las contribuciones del prefijo y de la continuación da:

    actionDifference L p q = squareActionDefect L d.

Si L satisface el ElementaryEulerLagrange histórico, se obtiene igualdad de
acciones para cada paso y, por inducción, para cualquier ruta p -> q.

Este es un consumidor interno del fundamento, no una interfaz que recibe la
conclusión como dato. La igualdad de acción no identifica las rutas de
intercambio. Tampoco prueba que cualesquiera dos historias estén conectadas.

## 5. Qué se ha ejecutado y qué no

25 tests Python pasan: 16 controles finitos y 9 controles de conservación de
fuentes e interfaces. Incluyen los seis caminos, doce intercambios dirigidos,
rechazo de dependencias/conflictos/repeticiones/índices inválidos, contextos,
fórmulas del observador en todos los valores de ZMod 5, defecto de acción
contextual y una mutación no estacionaria. La sintaxis Python se comprobó.

Son modelos finitos independientes y controles textuales/byte-exact, NO una
elaboración de Lean. Se trabajó con archivos exactos seleccionados obtenidos
por el conector GitHub, no con un checkout completo hidratado. Lean y Lake no
están disponibles; la descarga del compilador falló por resolución DNS.

No se ejecutaron:

- la elaboración de las nuevas pruebas Lean;
- las 22 salidas reales de #print axioms del arnés;
- source_audit.py sobre todo el repositorio y su cierre global de imports;
- la compilación completa del workspace ni consumidores ECIA;
- una revisión independiente de otra persona/agente.

Los logs, hashes, procedencia y alcance están en verification/cx-i1.
Los resultados no cierran automáticamente las filas históricas ni las 96 de CX.

## 6. Validación local preparada

Desde el checkout de CausalGeometry con el incremento:

```bash
python3 tools/verify_cx_i1.py --plan
python3 tools/verify_cx_i1.py
```

El segundo comando contrasta los hashes del incremento, exige el compilador
real, ejecuta la suite, reutiliza tools/source_audit.py, compila el cono
seleccionado y los consumidores QuasiNoether/CausalMomentumMap, y ejecuta el
arnés de axiomas. El recibo registra SHA, versión, dependencia mathlib
resuelta, logs y tiempos, con afinidad máxima de dos CPU disponibles.

Una ejecución exclusivamente no-kernel está disponible:

```bash
python3 tools/verify_cx_i1.py --non-kernel
```

Aunque todos los tests pasen, este modo devuelve 3: typecheck pendiente.
La falta de Lean/Lake también devuelve 3. Un fallo requerido devuelve 1.
El modo completo del incremento solo devuelve 0 tras el alcance Lean previsto;
no acredita por sí solo todo CX, una auditoría independiente o todo el workspace.

No se ha alterado el runner global existente. Este verificador añade un alcance
dirigido y conserva los resultados en directorios únicos sin borrar fallos.

## 7. Complejidad real del primer productor

Este incremento es un núcleo formal con un control finito, no una afirmación
HPC. La concatenación causal recorre su primer camino. Step.position calcula
prefix.length: no es O(1) con esta representación. Observar una ruta de ell
intercambios puede costar O(sum(longitud de sus prefijos)), acotado por
O(ell*h) cuando todos los prefijos tienen longitud <=h.

Route.positions usa append de un singleton en cada paso, por lo que su
materialización es O(ell^2) con listas enlazadas. Se utiliza como observador
formal del control; no se declara normalizador eficiente. Un acumulador
reverso/caché certificado es una mejora posterior que debe mantener sus
leyes, y no justifica una afirmación de rendimiento ahora.

El modelo solo materializa seis historias de tres eventos; no autoriza a
materializar h! historias para entradas generales. Los certificados y sus
contextos deben contarse aparte de la salida observada. No hay benchmark
publicado de normalización, trenzas generales o representación tensorial.

## 8. Cobertura y siguiente incremento

CX00: inventario parcial del cono necesario, APIs nativas contrastadas en
v4.32.1. CX01.01–05: primer sector cronológico fuente escrito. CX02.01–03:
caminos libres y contextos fuente escritos. CX04.01–02: discriminador y control
finito fuente escritos. CA09/CA21: consumidor variacional fuente escrito.
Todo ello sigue pendiente de elaboración/acreditación.

No quedan cerrados los intercambios paralelos o de factorizaciones, el grupoide
de inversos, la bicategoría completa de diarios, los cocientes de coherencia,
los sectores braid/symmetric/cactus, Garside, celdas superiores ni ECIA.

Tras elaborar y reparar este alcance, CX-I2 debe construir relaciones entre
rutas paralelas, la congruencia contextual generada, el cociente y su
propiedad universal. Así se podrá demostrar exactamente qué observadores
factorizan por imponer la relación ternaria y cuáles no. La preservación del
observador de offset cero y la exclusión del de offset dos darán un primer
control conectado al productor de CX-I1, no un ejemplo nuevo desligado.

El frente ECIA podrá consumir este productor una vez validado en su dominio,
sin exigir terminar toda la aritmética, las trenzas o la teoría superior.
