# CX-I4 — Operadores locales de aridad general y realización causal de Artin

Fecha: 2026-09-28. Rama: CausalGeometry/main.
Base consultada: 176ed316ed33f8413053addc3c6294eef8872aca.
Última entrega CX anterior: df76ae390db511fce90cdbab975834034104b5fa.
Estado: SOURCE-WRITTEN / NON-KERNEL-PASS / LEAN-TYPECHECK-PENDING.
Nuevas filas acreditadas: 0. No hay consumidor ECIA nuevo en esta entrega.

## 1. Alcance y conservación

Se añaden cinco módulos, sin cambiar los productores de CX-I1/I2/I3:

- Exchange/LocalOperator.lean: operadores de dos componentes, extensión local a listas de tamaño probado y leyes en todas las posiciones válidas.
- Exchange/ArtinPresentation.lean: presentación positiva de Artin para n generadores y n+1 componentes, acción construida y cociente adicional por cuadrados.
- Exchange/CausalOperator.lean: interpretación de intercambios causales reales en fibras cuyo tamaño es la longitud de la historia; contextos y extensión reversible.
- Exchange/CausalArtin.lean: realización posicional de historias causales de aridad fija en la presentación de Artin y cuadrado de interpretación.
- Models/ExchangeOperatorControls.lean: flip, copia no invertible, involución no-YB, Hurwitz para grupos arbitrarios y consumidores de las rutas causales anteriores.

El núcleo continúa partiendo de EventSystem. Las listas utilizadas por los operadores son fibras de observación, no nuevas historias primitivas ni datos añadidos a CausalNumber. ArityHistory conserva un CausalPath y una prueba de su longitud; no sustituye sus eventos/habilitación por una palabra sin semántica.

Se conserva la raíz actual completa y se añaden cinco imports. La raíz ya contenía dos imports nuevos del trabajo paralelo de procedencia aritmética local. Ambos se preservan. El resto de esos avances no se modifica ni se atribuye a este incremento. Los tests/manifiestos anteriores permanecen inmutables; las regresiones usan una proyección de raíz explícita y comprobada por hashes, que no equivale a compilar el agregado completo.

## 2. Operador básico y frontera de aridad

Para cualquier tipo A y función R:A×A -> A×A, stepList aplica R a dos entradas consecutivas, conservando el resto. R no presupone inversos, simetría o Yang–Baxter.

El helper total deja sin cambio un índice que no dispone de dos entradas. Esta totalización NO permite eliminar la hipótesis de tres posiciones en la relación de trenza. Con el flip y una lista de longitud dos, R0 R1 R0 e R1 R0 R1 difieren porque R1 sería identidad fuera de rango. Se incluye un teorema de rechazo de esa generalización falsa.

La API pública de la presentación usa:

    i : Fin n
    xs : {xs : List A // xs.length = n+1}.

Así el último índice inválido no es representable. La igualdad de trenza para i,j necesita i+1=j y sus pruebas de pertenencia a Fin n, que suministran la tercera posición.

Se escriben pruebas de preservación de longitud, compatibilidad con prefijos (desplazando el índice), compatibilidad con sufijos bajo la cota de dos posiciones, conmutatividad lejana sin YB, elevación de YB desde triples y elevación independiente de inversas. Todas están pendientes de elaboración Lean.

## 3. Familias completas de Artin por rango

El quiver tiene un objeto dedicado y n generadores, no una nueva categoría manual. Se reutilizan CategoryTheory.Paths y CategoryTheory.Quotient. La familia Relation n contiene exactamente:

    sigma_i sigma_j = sigma_j sigma_i      si i+1<j;
    sigma_i sigma_j sigma_i = sigma_j sigma_i sigma_j  si i+1=j.

Los índices pertenecen a Fin n. La primera orientación es suficiente porque el cociente genera la equivalencia simétrica. No se introducen inversos ni sigma_i²=1 en la presentación positiva. n=0 está admitido y no tiene generadores.

Una prueba YangBaxter R sobre A³ produce operator_respects para TODO n. positiveAction se construye mediante el descenso I2, y positiveAction_square demuestra el cuadrado con la interpretación de palabras. No se almacena la existencia de la acción como un campo.

Squares n es una familia separada. Si R es también involutivo, se construye symmetricAction sobre el cociente ampliado, y toSymmetric es el comparador desde la presentación positiva. Esto no es una afirmación de fidelidad, una normalización de trenzas ni un teorema de equivalencia geométrica con configuraciones de hebras. Tampoco equipa automáticamente toda una categoría de un trenzado monoidal natural.

## 4. Conexión con los productores causales

CausalOperator.prefunctor asigna a cada CausalPath p una fibra de exactamente p.length entradas. Para un Step p q, utiliza SU posición derivada y la prueba Step.position_bound. Step.length_eq garantiza que el estado resultante pertenece a la fibra correcta de q.

Esta interpretación existe para cualquier R, incluso cuando YB falla. Se extiende por la categoría libre ya construida. Las compatibilidades de prefijo y sufijo utilizan los contextos causales, no solamente concatenaciones de palabras abstractas.

Si R procede de una equivalencia real en A×A, corePrefunctor construye isomorfismos entre las fibras dependientes con las inversas verificadas. reversibleAction consume entonces el grupoide libre de I3. La igualdad sobre rutas positivas reutiliza Reversible.positive_extend. No se invierten eventos primitivos.

CausalArtin toma el dominio de historias de longitud n+1. Su índice Fin n se DERIVA del Step real y su cota. El funtor de palabras y la proyección a la presentación positiva dan una realización:

    caminos de intercambios causales de aridad fija -> presentación positiva de Artin.

Para un operador YB, realizar primero e interpretar después coincide con interpretar sus palabras posicionales. La igualdad de imágenes por esa realización implica igualdad de las observaciones que factorizan por ella; NO implica igualdad de rutas fuente. Esta distinción se conserva como teorema y frontera explícita.

Falta todavía demostrar una clasificación intrínseca de todas las coherencias del dominio causal y cualquier fidelidad de esa realización. No se declara que todo sistema de eventos satisfaga relaciones de trenza por construcción.

## 5. Controles y resultados matemáticos nuevos

### Sectores independientes

- Flip: YB e involutividad; produce acciones positivas y del cociente con cuadrados.
- R(a,b)=(b,b): YB sin inyectividad; produce la acción positiva sin fingir inversas.
- R(a,b)=(not a,b), sobre Bool: involutivo pero no YB. En las rutas de I1, desde [false,false,false], los resultados son [false,true,false] y [true,false,false]. Son las mismas historias causales reales del modelo anterior.
- Flip fuera del rango admitido: control que refuta quitar la cota de aridad.

### Hurwitz sin restringir el teorema a S3

Para todo grupo G:

    H(a,b)=(aba^-1,a),
    H^-1(u,v)=(v,v^-1 u v).

Se escriben pruebas algebraicas de las dos inversas, YB, conservación del producto de la pareja y conservación del producto ORDENADO de toda lista bajo un operador local. La realización positiva existe en cualquier rango mediante los productores anteriores.

causal_hurwitz_product demuestra, por inducción sobre una Route causal real, que su interpretación conserva el producto ordenado de la fibra. No afirma que todo grupo sea un objeto elíptico/arimético ECIA ni que cualquier factorización de igual producto esté en la misma órbita. La realización no borra la distinción entre ocurrencias causales y factores observados.

## 6. Validación ejecutada

Se ejecutó primero la suite I3: 71 tests PASS. La suite nueva contiene 20 controles finitos y 8 contratos de fuentes, más todos los 71 anteriores: 99 tests PASS. El primer ensayo y la reejecución final pasaron; se preservan ambos logs.

El censo finito examinó las 256 funciones Bool² -> Bool²: 43 satisfacen YB; entre las 24 biyecciones, 5 satisfacen YB. Hay 10 involuciones y 7 no satisfacen YB. Estos son resultados de la enumeración ejecutada, no conteos de teoremas Lean. Para los 43 operadores YB se comprobó la elevación en tamaños 3..6; para Hurwitz en S3, todos los 216 triples y productos de listas de tamaños 1..4.

Pasan también sintaxis Python, controles negativos del manifiesto ausente/hash incorrecto (salida 1), gate no-kernel (salida 3) y detección real de Lean/Lake ausentes (salida 3). La red del contenedor no resuelve github.com. No se simuló un compilador ni se atribuye independencia a la revisión del autor.

Pendientes: elaboración Lean, 37 nuevas salidas de #print axioms (133 acumuladas), auditoría global de fuentes/imports, workspace completo y consumidor ECIA. Los archivos se montaron desde los incrementos anteriores y se reconciliaron con la raíz actual por hash; no hay checkout completo hidratado.

## 7. Complejidad y evidencia

No se ha enumerado el monoide de trenzas ni construido un normalizador. La presentación y su propiedad universal son construcciones formales.

Para listas persistentes, aplicar el helper hasta la posición i visita un prefijo de longitud O(min(i,h)); se añaden el coste C_R de R y los nodos del prefijo reconstruido. Los sufijos pueden compartirse. Esta es una cuenta de la representación definida, no una medición de código Lean compilado. La representación Python con tuplas copia también sufijos y cuesta O(h+C_R) por paso; no se confunden ambos modelos de coste.

Para una ruta de longitud ell, una cota conservadora del observador es O(ell*(h+C_R)), más el coste de obtener las posiciones y del crecimiento de sus coeficientes. El producto de Hurwitz usa operaciones del grupo; representaciones de enteros/matrices deben contabilizar coste de bits y densificación por separado. No se promete un algoritmo polinómico para igualdad o conjugación de presentaciones arbitrarias.

La suite exhaustiva booleana escala como |A|^(2|A|²) funciones y no se propone como método general de certificación. La prueba algebraica es el objetivo Lean; el censo es un control adversario pequeño.

## 8. Ejecución local

En el checkout actualizado:

```bash
python3 tools/verify_cx_i4.py --plan
python3 tools/verify_cx_i4.py
```

Solo controles independientes:

```bash
python3 tools/verify_cx_i4.py --non-kernel
```

El último modo devuelve 3 aunque pase la suite. El gate completo exige Lean real, hashes exactos, auditoría de fuentes, el cono de dependencias y los cuatro arneses. Conserva recibos y logs únicos, afinidad máxima de dos CPU y conteo explícito de las salidas de axiomas. Un PASS de ese alcance no acreditaría por sí solo todo CX.

## 9. Fronteras que siguen abiertas

La presentación positiva de rango general y sus acciones están escritas; no se cierran automáticamente el grupo de trenzas geométrico, Garside/Ore, el sector cactus, la coherencia superior o todos los diagramas intrínsecos del núcleo. Tampoco se sustituye la campaña causal original por este nuevo sector.

La próxima prioridad es elaborar y reparar el alcance acumulado y completar los comparadores entre la realización posicional y las coherencias intrínsecas fuente, con pruebas de conservación/pérdida. ECIA puede consumir esos productores en un frente paralelo; esta entrega no incluye ni afirma ese consumidor.
