# CX-I5 — Comparación causal directa y transporte de coeficientes Phi/Psi

Fecha: 2026-09-28. Rama: CausalGeometry/main.
Base: b9659ab2fff5a6d97124259019ff627ad97d8e05.
Código/manifiesto: 5a140c8cb1ee153ef94b76576c5a23bf8314a234.
Estado: SOURCE-WRITTEN / 127 NON-KERNEL TESTS PASS / LEAN-TYPECHECK-PENDING.
Nuevas filas acreditadas: 0. No se implementa aquí un consumidor ECIA.

## 1. Problema que resuelve este incremento

I4 construyó la acción sobre fibras de caminos causales y la acción posicional
que desciende por Artin. Su realization_square comparaba dos construcciones
posicionales. I5 añade el comparador que faltaba con la acción causal definida
independientemente, y desarrolla cambios de coeficientes compatibles con ambas.

Se conservan todos los productores, tests, manifiestos y runners I1–I4. Solo
se añaden cinco imports a la raíz y un apartado al índice documental. No se
cambia EventSystem, CausalNumber, PairedTransform, los pins ni las otras ramas.
No se añaden workflows ni se modifica el runner global. Las realizaciones
ECIA siguen siendo un frente paralelo con obligaciones propias.

Módulos nuevos:

- Exchange/OperatorTransport.lean: cuadrados de coeficientes, elevación local,
  transferencia/reflexión de Yang–Baxter con sus hipótesis.
- Exchange/CausalOperatorTransport.lean: transformaciones naturales sobre las
  rutas causales reales y compatibilidades independientes del par Phi/Psi.
- Exchange/ArtinOperatorTransport.lean: transporte natural en palabras y en la
  acción positiva de Artin mediante el cociente nativo.
- Exchange/CausalArtinComparison.lean: reificación de rutas existentes y
  comparación natural de la acción causal con la acción posicional.
- Models/ExchangeTransportControls.lean: controles de pérdida, independencia
  de direcciones, recorridos no inversos y homomorfismos/Hurwitz.

Las pruebas están escritas; su elaboración Lean aún no se ha ejecutado.

## 2. Cuadrado local y extensión a rutas

Para f:A->B y operadores R:A²->A², T:B²->B²:

    Intertwines f R T  iff  (f×f)(R(x)) = T((f×f)(x)) para todo x.

Este predicado no incluye inversas, inyectividad, sobreyectividad o YB.
Se escriben pruebas de identidad y composición, y de que el cuadrado local
se eleva a stepList en todas las posiciones, incluidas las identidades fuera
de rango del helper total. La acción pública sigue utilizando sus índices
admitidos; no se retira la cota ternaria de I4.

mapSized conserva el tamaño certificado. La inducción sobre Exchange.Route
produce map_route y la transformación natural transport entre los funtores
CausalOperator.action existentes. Se construyen sus leyes de identidad y
composición mediante los tipos nativos NatTrans. Para una equivalencia real
de coeficientes se obtiene transportIso mediante NatIso.ofComponents.

ArtinOperatorTransport repite el argumento para palabras, y desciende esa
transformación al cociente positivo mediante la inducción nativa de Quotient.
Las leyes YB de ambos operadores son hipótesis explícitas de ese descenso.

## 3. Dos construcciones de la acción, ahora comparadas

actualAction se define como forgetPaths seguido de CausalOperator.action;
no utiliza la acción de Artin como definición. positionalAction utiliza el
funtor de palabras posicionales y Artin.wordAction.

reifyRoute añade certificados de aridad a una ruta causal ya existente.
Las aridades intermedias se derivan de Route.historyLength_eq. El resultado
forget_reifyRoute recupera exactamente la ruta original: no se sustituyen
los eventos ni los certificados Step por una palabra de índices libre.

castSize transporta solo el certificado de tamaño y deja intacta la lista.
Las pruebas actual_positional_values y actualPositionalIso comparan ambas
acciones para toda ruta y todo estado admitido. Esta comparación NO exige YB;
el operador toggleFirst que la incumple sigue teniendo ese comparador.

Al añadir YB, actualArtinIso compara la acción genuinamente causal con la
acción después de la realización de Artin. Se deriva entonces:

    misma imagen de Artin => mismo operador en las fibras causales;
    operadores causales distintos => imágenes de Artin distintas.

No se deduce fidelidad de las rutas fuente ni una clasificación intrínseca
de todas sus coherencias. Inyectividad del cambio de coeficientes, fidelidad
de un funtor e inyectividad de una representación de rutas son propiedades
diferentes.

## 4. El par estructural se consume sin cambiar sus axiomas

Compatible P R T exige dos cuadrados separados:

    Intertwines P.forward R T;
    Intertwines P.backward T R.

Se construyen las dos transformaciones naturales y se prueba compatibilidad
con la composición histórica del par: forward compone covariantemente;
backward, en el orden contrario. Ambos recorridos del par entrelazan el
operador y conmutan con la acción sobre rutas.

Nada de ello implica que esos recorridos sean identidad. El control de
coeficientes Bool con ambas direcciones constantes false y el flip satisface
los dos cuadrados, pero modifica el estado [true,true,true]. El teorema sobre
su recorrido se consume sobre la route121 real de I1.

Otro control usa fuente copyRight, destino flip, Phi constante false y Psi=id.
Phi entrelaza, Psi no. Ambos operadores satisfacen YB: no basta esa coincidencia
para deducir compatibilidad de las dos direcciones.

Este incremento trata compatibilidad funcional exacta. No implementa todavía
la identidad lineal aditiva de D_R, una adjunción ordenada universal, dagger,
transporte Hodge ni todos los defectos de la campaña.

## 5. Hipótesis exactas para mover la ley Yang–Baxter

Se escriben dos teoremas distintos:

- f entrelaza y es inyectiva: YB en el destino refleja YB en la fuente.
- f entrelaza y es sobreyectiva: YB en la fuente da YB en todo el destino.

El primer control de frontera proyecta Bool en Unit y envía toggleFirst,
que falla YB, al operador único del destino, que la satisface. Un observador
no inyectivo puede esconder el fallo de coherencia de su fuente.

El segundo usa Phi constante false de Bool a Bool: entrelaza el flip con
controlledNot, que fija (false,false) pero falla YB fuera de esa imagen.
Una interpretación sobre una imagen propia no acredita una ley global del
destino. El ejemplo conserva el mismo portador en ambos lados.

Estos controles son también pruebas escritas sobre los modelos finitos en
Lean; la comprobación Python no sustituye su elaboración.

## 6. Homomorfismos y Hurwitz

Para cualquier homomorfismo de grupos f:G->*H se prueba que su aplicación
componente a componente entrelaza los operadores Hurwitz de G y H. Se usa
la conservación de productos e inversas del homomorfismo, no un campo libre
que reciba el cuadrado como conclusión.

causal_hurwitz_hom consume el resultado para toda ruta causal admitida;
positiveHurwitzTransport construye el morfismo entre las acciones positivas
en cualquier rango. El control finito utiliza el homomorfismo de paridad
S3->C2. Eso no identifica automáticamente este destino con un objeto ECIA.

## 7. Validación realmente ejecutada

La suite inicial I4 pasó sus 99 tests. La nueva suite pasa 127: 20 controles
finitos nuevos, 8 contratos de fuentes nuevos y los 99 anteriores intactos.
El primer ensayo y la reejecución final pasaron. Se comprobó sintaxis Python.

El censo independiente examina 256 operadores fuente, 256 operadores destino
y 4 mapas Bool->Bool: 262144 cuadrados candidatos. Hay 33280 que entrelazan,
512 con mapa inyectivo y 32768 no inyectivos. El resultado es una enumeración
finita, no una clasificación Lean acreditada de todo el formalismo.

La comparación actual/posicional finita usa dos cálculos: uno recupera cada
posición de las diferencias entre historias de ocurrencias; el otro interpreta
la palabra de posiciones. Se comprueban los 256 operadores, seis palabras y
ocho estados ternarios. Se añaden controles de aridad, contextos y homomorfismos.
Este modelo no demuestra que represente todos los certificados Step posibles.

Los diez blobs publicados del payload se contrastaron con los archivos
ensayados. Dos errores de transcripción de la raíz fueron detectados y
corregidos en árboles sin referencia antes del commit de código; no se
adaptaron los tests ni se modificó el contenido local correcto para aceptarlos.

El trabajo usa los ZIP montados de I1–I4 y archivos seleccionados exactos del
conector. Un repositorio Git local auxiliar sirve únicamente para generar el
parche: NO es un checkout completo de GitHub ni evidencia del SHA remoto.
Se retiró ese Git auxiliar durante la ejecución final del runner; el recibo
original registra source_sha=null. La procedencia remota la dan los blobs
contrastados y el SHA del commit fuente, no un identificador local sintético.

Lean y Lake no están disponibles; el acceso de red no resuelve github.com.
No se ejecutaron elaboración, auditoría global de imports/fuentes, workspace
completo, consumidores ECIA ni las 193 salidas de axiomas solicitadas
(22+36+38+37+60). No se afirma revisión independiente ni acreditación nueva.

## 8. Verificador y ejecución local

Desde el checkout actualizado:

```bash
python3 tools/verify_cx_i5.py --plan
python3 tools/verify_cx_i5.py
```

Solo para controles independientes:

```bash
python3 tools/verify_cx_i5.py --non-kernel
```

Ese modo devuelve 3 aunque todos los tests pasen. El gate completo exige
Lean real, comprueba hashes antes y después, compila el alcance declarado,
reutiliza source_audit.py y ejecuta los cinco arneses. Manifiesto ausente o
hash incorrecto devuelve 1; toolchain ausente devuelve 3. Esos rechazos se
probaron sin simular un compilador. Los logs/recibos usan directorios únicos.

## 9. Costes y frontera siguiente

Mapear una fibra de h componentes cuesta O(h*C_f) tiempo y O(h) nueva memoria
con listas explícitas. El comparador de tamaño conserva los valores; el coste
de su elaboración y de certificados dependientes no se ha medido. La acción
en rutas mantiene los costes de acceso/listas de I4; no se anuncia una mejora
HPC ni un normalizador por añadir estas pruebas de compatibilidad.

El censo booleano es exhaustivo solo porque su dominio es finito y pequeño.
Para portadores de tamaño a,b, enumerar todas las funciones/operadores crece
con b^a*(a²)^(a²)*(b²)^(b²). Este procedimiento no se propone como solver
general. Invariantes, certificados y teoremas locales son mecanismos distintos.

La siguiente obligación prioritaria de acreditación sigue siendo ejecutar
Lean y corregir el alcance acumulado. El desarrollo matemático restante
incluye los defectos lineales D_R, comparaciones reversibles generales,
coherencias intrínsecas, Garside/cactus y realizaciones ECIA reales. Ninguno
se da por completado al demostrar una comparación de coeficientes.
