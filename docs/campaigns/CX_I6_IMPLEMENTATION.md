# CX-I6 — Defectos causales lineales, tensoriales y compatibilidad diferencial

Fecha: 2026-09-29. Repositorio/ramal: CausalGeometry/main.
Base: 9171badcbb3617e1221975f3dc1fd3f7859b7713.
Código/manifiesto: 3e61dd843ebbdc961ed67d0f118953632fbf1f93.
Estado: SOURCE-WRITTEN / 159 NON-KERNEL TESTS PASS / LEAN-TYPECHECK-PENDING.
Filas nuevas acreditadas: 0. No se modifica ECIA ni GenContinuum.

## 1. Construcción acumulativa

I5 trataba cuadrados de transporte que conmutan exactamente. I6 conserva ese
sector y construye el defecto cuando no conmutan. No exige invertibilidad,
adjunción, Yang–Baxter o dimensión finita para definir esos fallos.

Cinco módulos nuevos:

- Calculus/LinearSquareDefect: cuadrados lineales heterogéneos, composición
  horizontal/vertical y mayor submódulo de compatibilidad puntual.
- Calculus/GradedDefectCompatibility: comparación con el defecto diferencial
  de CA21, identidad diferencial y exactitud sobre cociclos.
- Exchange/TensorTransportDefect: producto tensorial nativo, regla D(GF),
  términos cruzados de F+G y defectos separados de ambos recorridos Phi/Psi.
- Exchange/LinearizedCausalAction: módulo libre nativo sobre las fibras de
  las historias existentes; defectos sobre rutas reales y cambios de coeficientes.
- Models/ExchangeLinearDefectControls: controles conectados a I1–I5 y modelos
  lineales que rechazan cancelaciones y dominios indebidamente promovidos.

No se reescriben los productores I1–I5, los manifiestos históricos, EventSystem,
PairedTransform o CausalNumber. La raíz añade exactamente cinco imports.
Tampoco se crea una segunda teoría de cochains: se consume
GradedLinearTransport.defect y se compara por igualdad de definiciones.

## 2. Cuadrados lineales, no solo endomorfismos

Sean a:A0→A1, b:B0→B1 y transportes F0:A0→B0, F1:A1→B1.

    D(a,b;F0,F1) = b F0 - F1 a.

Se escribe la prueba de cero si y solo si el cuadrado conmuta. El ámbito
algebraico usa módulos sobre un anillo conmutativo; no necesita un cuerpo.

Pegar transportes horizontalmente da:

    D(GF) = D(G) F0 + G1 D(F).

Pegar pasos de proceso verticalmente da:

    D(a'a,b'b;F0,F2) = b' D(a,b;F0,F1) + D(a',b';F1,F2) a.

Ambas leyes son identidades de mapas, no aproximaciones numéricas. Permiten
reconstruir el defecto compuesto desde defectos locales SIN suponerlos nulos.
Los signos importan: dos términos no nulos pueden cancelarse.

## 3. Tensor genuino y par estructural

Para F:A→B lineal se usa TensorProduct.map F F. El sector tensorial define

    D_R(F) = R_B (F⊗F) - (F⊗F) R_A,
    D_R(GF) = D_R(G) (F⊗F) + (G⊗G) D_R(F).

Se obtienen fórmulas separadas para Psi Phi y Phi Psi. Los dos mapas se pueden
olvidar al PairedTransform histórico, sin exigir que sean inversos.

El mapa F↦F⊗F NO es aditivo. Se escriben sus términos cruzados:

    (F+G)⊗(F+G) = F⊗F + F⊗G + G⊗F + G⊗G.

El test escalar racional distingue 4 de 2 cuando se intenta eliminar esos
sumandos. La aditividad del cuadrado en (F0,F1) no justifica una aditividad
falsa del defecto tensorial en F.

Este sector tensorial y el módulo libre del apartado siguiente no se
identifican por decreto. Un comparador monoidal entre ambos, cuando proceda,
será un resultado adicional; no está supuesto por compartir la palabra lineal.

## 4. El defecto actúa sobre rutas causales reales

Se compone CausalOperator.action, definido antes de Artin, con ModuleCat.free.
Un estado x de la fibra de una historia se convierte en el generador [x] de
su módulo libre. No se enumeran todas las historias ni se añade un estado
vectorial como nueva primitiva ontológica.

Para r:p⇒q y un cambio de coeficientes f se construye

    D_r(f) = L_T(r) L(f_p) - L(f_q) L_R(r).

Sobre un generador de estado:

    D_r(f)[x] = [T(r)(f_p(x))] - [f_q(R(r)(x))].

Con coeficientes en un anillo no trivial, ese mapa es cero exactamente cuando
los dos cálculos funcionales coinciden sobre TODOS los estados. La hipótesis
1≠0 se conserva: en el anillo trivial la linealización no separa nada.

La compatibilidad de I5 implica defecto cero, por consumo del teorema anterior
map_route. Sin compatibilidad, siguen existiendo el mapa y las identidades:

    D_(t r)(f) = L_T(t) D_r(f) + D_t(f) L_R(r),
    D_r(g f) = D_r(g) L(f_p) + L(g_q) D_r(f).

Se especializa la segunda fórmula a las direcciones del PairedTransform
original. La ruta identidad tiene defecto cero. Ni los defectos locales ni
su suma se reinterpretan como normas o valores absolutos.

## 5. Controles de información y estabilidad

En la route121 real, con cambio identidad, fuente flip y destino toggleFirst,
el estado [false,false,false] da el defecto

    [false,true,false] - [false,false,false].

Es no nulo en el módulo libre racional. Intercambiar fuente y destino produce
un defecto no nulo de signo contrario; el recorrido compuesto puede tener
cero defecto. Por tanto, cero defecto del recorrido no acredita las etapas.
El par forwardOnly de I5 también conserva su asimetría: Phi compatible y Psi
incompatible. El par collapsingPair es compatible pero no es una equivalencia.

La augmentación que suma todos los coeficientes anula CADA defecto D_r(f).
Este es un teorema general escrito, no solo el resultado de un ejemplo:

    epsilon ∘ D_r(f) = 0.

La conclusión no es que el defecto sea cero. Es que esa observación escalar
es incapaz de detectarlo. Los coeficientes son formales y pueden ser negativos;
no se añade una interpretación probabilística.

El núcleo de un defecto es el mayor submódulo donde ese cuadrado conmuta
puntualmente. Pero no es necesariamente estable por la dinámica. Un control
en Q² toma a(x,y)=(y,x), b(x,y)=(y,x+y) y F=id: D(x,y)=(0,y).
El vector (1,0) pertenece al núcleo y a(1,0)=(0,1) no. Para propagar
compatibilidad local hace falta también compatibilidad del estado intermedio.
No se anuncia ya construido el mayor dominio estable bajo todos los contextos.

## 6. Conexión con CA21: evitar una obstrucción cohomológica vacía

Se reutiliza el defecto diferencial D_n=d_B F_n-F_(n+1)d_A de CA21. Los
square-zero de los complejos existentes dan la identidad

    d_B D_n + D_(n+1) d_A = 0.

Si x es un cociclo, D_n(x)=d_B(F_n(x)). Por tanto, el defecto bruto es exacto,
cerrado y su clase en el cociente cohomológico YA EXISTENTE del destino es cero.
Se construyen los testigos de imagen y la prueba defect_closed_class_zero.

Eso no prueba que F sea mapa de complejos: la exactitud de un vector no es su
anulación. Tampoco elimina posibles obstrucciones relativas, filtradas o de
levantamiento con datos extra. Únicamente impide llamar nueva clase no trivial
a este conmutador bruto evaluado sobre un cociclo.

## 7. Validación y procedencia

El entorno contiene los ZIP incrementales I1–I5, no un checkout completo.
La primera ejecución de la suite anterior dio 126 éxitos y un error de archivo
ausente: PairedTransform.lean no formaba parte de los ZIP incrementales. Se
recuperó por el conector en el SHA base y se verificó el blob Git
6ee6735ce2d962ba4f0562911993011a7cb0a8b8. No se modificó ese productor ni el test.
Después pasaron los 127 tests anteriores.

La suite nueva pasa 159: 24 controles exactos nuevos, 8 contratos de fuente y
127 regresiones intactas. Usa Fraction y matrices rectangulares para evitar
que la coincidencia dependa de redondeo o de dimensiones accidentalmente iguales.
Hay 64 cuadrados horizontales, 64 verticales, 16 composiciones tensoriales y
familias finitas de operadores/fibras causales, además de controles de frontera.
Esos casos NO prueban por enumeración los enunciados Lean generales.

Se ejecutaron sintaxis Python, gate no-kernel (salida 3), detección real de
Lean/Lake ausentes (salida 3) y rechazo de manifiesto ausente/alterado (salida 1).
El compilador no se simuló. No se ejecutaron elaboración, auditoría global,
workspace completo, realizaciones ECIA ni los 252 outputs de axiomas preparados.
Hay 59 nuevas solicitudes; dos vuelven a observar productores CA21 históricos.

La evidencia original guarda source_sha=null porque no hay checkout upstream.
Los blobs publicados se contrastan con los archivos ensayados. Un Git auxiliar
para generar/verificar un parche no se utiliza como evidencia del SHA remoto.
No se atribuye independencia a la revisión estática realizada por el autor.

## 8. Contrato de recursos

Para a:K^a0→K^a1, b:K^b0→K^b1, F0 y F1 compatibles en tamaño, formar D con
matrices densas cuesta O(b1*b0*a0 + b1*a1*a0) operaciones escalares y O(b1*a0)
entradas de salida, aparte de los operandos. Bits de racionales y costes de
multiplicación/reducción se contabilizan aparte. Aplicar D a un vector puede
hacerse como dos rutas sin materializar D.

Para dimensión d por componente, un operador en A⊗A ocupa d^4 coeficientes;
la multiplicación densa ingenua puede costar O(d^6). La existencia de la
identidad D(GF) no prueba que materializar esos operadores sea eficiente.

La linealización libre de una fibra de h posiciones y alfabeto de a elementos
tiene dimensión a^h si se enumera su base. No se recomienda esa enumeración.
Con z estados de soporte y acciones deterministas, aplicar las dos rutas a
un vector disperso produce como máximo 2z etiquetas antes de fusionarlas:
el coste es el de evaluar esas rutas y reunir etiquetas, incluyendo h, la
longitud ell de ruta, búsquedas y aritmética exacta. No se afirma una cota
polinómica independiente de la representación o del tamaño de salida.

Este incremento aporta teoremas e interfaces; no publica un benchmark HPC,
normalizador general ni solver de igualdad de rutas.

## 9. Gate actual y frontera siguiente

    python3 tools/verify_cx_i6.py --plan
    python3 tools/verify_cx_i6.py
    python3 tools/verify_cx_i6.py --non-kernel

El último modo devuelve 3 aunque todos los tests pasen. El gate completo
comprueba hashes antes/después, reutiliza source_audit.py y los arneses I1–I6.
Las evidencias históricas permanecen inmutables; se proyecta únicamente el
sufijo nuevo de la raíz con comprobación de hash para repetir sus tests.

Continúan pendientes la elaboración acumulada, las fronteras intrínsecas de
coherencia, el mayor dominio predictivo/contextualmente estable, Garside/cactus,
las comparaciones superiores y consumidores ECIA efectivos. I6 no los da por
cerrados por haber construido un conmutador lineal.
