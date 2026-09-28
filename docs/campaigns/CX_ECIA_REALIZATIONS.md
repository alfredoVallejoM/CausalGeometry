# CX — Realizaciones ECIA/GenContinuum en paralelo

Fecha: 2026-09-28. Estado: PLANIFICACION; no afirma nuevos consumidores implementados.
Fuente normativa: CX_EXCHANGE_COHERENCE.md. Filas principales: CX10.01–08, con dependencias locales.

## 0. Alcance y procedencia

Esta planificacion se publica en CausalGeometry/main para mantener una fuente documental comun. La implementacion downstream corresponde a GenContinuum, sin introducirlo como dependencia del nucleo causal.

Rama de adaptadores consultada el 2026-09-28:

    GenContinuum/campaign/causal-ecia-adapter
    3daaa362caf3bd6a78a44e9ad6d096c49c11b07d

La otra continuacion ECIA/Tamagawa y las rutas previas permanecen intactas. Esta entrega no cambia pins, no fusiona ramas, no actualiza codigo en GenContinuum y no impone su cierre como requisito del fundamento causal. Antes de cada implementacion se releeran los productores reales del destino; las referencias a sectores existentes no acreditan que toda la API necesaria este disponible.

CA-13.15 conserva el objetivo trenzado y recibe el fundamento mas general. CA-13.16 conserva la realizacion ribbon. CA-13.17 mantiene sus fronteras de Hecke/Markov y otras realizaciones avanzadas. CX no reemplaza los desarrollos de Frobenius, Tate, Bruhat–Tits, Ihara, Tamagawa, Selmer, operadoriales o espectrales.

## 1. La unidad de realizacion no es un numero aislado

Para cada dominio admitido D de fuentes, una realizacion debe producir objetos, historias y transformaciones compatibles. Un dato X solo como indice de una lista de destinos no demuestra procedencia intrinseca.

La estructura minima del consumidor debe explicitar:

* dominio fuente y fronteras;
* objetos reales del destino;
* imagen de historias/diarios;
* imagen de intercambios elementales;
* extension composicional a rutas;
* relaciones de la fuente que respeta;
* comparadores de producto/asociacion cuando correspondan;
* observadores y perdida que se reclaman.

En un sector con fronteras A,B, usar un funtor sobre la categoria local de historias/intercambios. Para afirmar compatibilidad con composicion de diarios entre fronteras distintas, demostrar los comparadores y coherencias de esa composicion. No llamar pseudofuntor al dato de un funtor local sin esos teoremas.

La codificacion del nivel debe ser literal. Un mapa de configuraciones no es un mapa de historias; un funtor sobre historias no es automaticamente fiel en transformaciones; una igualdad en el destino puede corresponder a una 3-celda en un consumidor superior. Cada comparacion indica si afirma igualdad estricta, isomorfismo, equivalencia, o existencia de un comparador de dimension superior.

## 2. D0 — Primer consumidor de rutas con informacion visible

Dependencias: CX01, CX02.01–03, un modelo CX04. No depende de Garside, ribbon ni completaciones.

Elegir un destino nativo donde las rutas actuen de forma no trivial sobre un portador finito o modulo. El portador debe provenir de una construccion ECIA declarada o estar unido a ella por un comparador real; no crear una estructura paralela llamada ECIAExchange que solo envuelva un tipo arbitrario.

Primer experimento: tres eventos concurrentes, dos rutas ternarias y el modelo de observacion ZMod 5 del documento principal. El destino conserva o pierde la diferencia 3/4 de manera demostrada. El alcance exacto es un modelo local de intercambios; no una reconstruccion de toda la fuente.

Teoremas de salida:

    interpret(id)=id
    interpret(Q o P)=interpret(Q) o interpret(P)
    interpret(P)(0)=3
    interpret(Q)(0)=4
    P != Q.

Control: un interprete de igual tipo que proyecta solo la permutacion produce imagenes iguales. Esto da una perdida explicita de informacion de rutas, no solo un resultado numerico de distinto valor.

El uso de fibras de observacion no modifica la ontologia de los eventos ni convierte el estado observado en dato primitivo de la fuente.

## 3. D1 — Operadores YB y trenzados, separados por dominio

Dependencias: CX03/04 y el producto nativo del destino elegido.

### D1-a: operador no invertible

Realizar R(x,y)=(y,y) o una version lineal explicitamente construida. Probar YB, conmutatividad lejana en potencias tensoriales y la accion de B_n^+ por la propiedad de la presentacion. No instanciar un BraidedCategory global ni una accion de B_n sin inversos.

### D1-b: operador invertible no simetrico

Realizar Hurwitz o un operador invertible concreto con YB y un testigo de doble intercambio no identidad. Construir la extension a B_n. Una representacion de B_n no es necesariamente fiel: su nucleo debe tratarse como perdida y no ocultarse.

### D1-c: trenzado natural

Para una realizacion monoidal fuerte F, fijar comparadores

    mu_(A,B): F(A) tensor F(B) -> F(A tensor B).

La compatibilidad correcta de trenzado es

    F(c_(A,B)) o mu_(A,B)
      = mu_(B,A) o c_(F(A),F(B)).

Asociadores, unidades y naturalidad deben ser los del destino. No comparar mapas cuya fuente sea respectivamente F(A tensor B) y F(A) tensor F(B) sin mu. No hay motivo para forzar estas igualdades a ser definicionales.

Teorema de frontera: si el destino satisface YB y el interprete de generadores es compatible, las imagenes de las dos rutas ternarias coinciden. Reflejar la igualdad exige fidelidad local. Si el origen tiene un defecto detectado, el consumidor trenzado es necesariamente no fiel en ese nivel.

## 4. D2 — Restriccion, filtraciones y Phi/Psi

Dependencias: CX05, CX07.05 y productores reales de restricciones/filtraciones.

Reutilizar mapas directos/inversos y las adjunciones que existan en GenContinuum. Demostrar por separado la compatibilidad de cada direccion con intercambios, grado y contexto. La existencia de una adjuncion entre niveles no prueba que los operadores de intercambio conmuten con ella.

En un sector lineal, construir los dos cuadrados de R con Phi tensor Phi y Psi tensor Psi. Usar la formula de composicion de D_R para interpretar los recorridos y posibles cancelaciones.

Requisitos adicionales:

* no todo intercambio de una historia fina desciende a una historia restringida;
* si desciende, probar independencia del representante;
* si diferentes intercambios descienden al mismo, publicar la perdida;
* si se exige levantar un intercambio del nivel grueso, construir el levantamiento o conservar su obstruccion;
* no identificar una inclusion de observadores con la adjunta de un operador Hilbert.

Control positivo: restriccion identidad. Control de perdida: dos rutas distintas que coinciden tras proyeccion. Control de obstruccion: un intercambio del destino sin representante en el dominio fuente elegido.

## 5. D3 — Factorizaciones y Hurwitz

Dependencias: CX04.04 y la realizacion de un dominio de factorizaciones fuente; CX06 cuando se usen fracciones.

El operador de Hurwitz

    (a,b) -> (aba^{-1},a)

conserva a*b. Su inversa es (u,v)->(v,v^{-1}uv). El programa debe transportar una factorizacion causal a un grupo o grupoide de destino y demostrar que el intercambio causal elegido se realiza por ese operador.

No basta dar una accion de Hurwitz en un grupo preexistente. Se requiere el cuadrado entre la transformacion de la factorizacion FUENTE y la transformacion de su imagen. Si la fuente no tiene inversos, no usar a^{-1} alli: probar una formula mediante complementos/residuos en un dominio adecuado o pasar por una localizacion ya justificada.

La pregunta estructural es ahora: cuales factorizaciones de un mismo compuesto estan conectadas por intercambios admitidos, que estabilizadores/monodromias quedan y que distingue sus orbitas. Igual producto no implica misma orbita. Igual orbita de un observador no implica misma orbita causal.

Destinos posteriores posibles: monodromia de recubrimientos, paquetes de degeneracion y estructuras aritmeticas construidas desde una fuente comun. Cada nombre exige un productor real del destino, no una analogia.

## 6. D4 — Ribbon, cierre y trazas

Dependencias: CX09 y los productores nativos del destino. Este frente no bloquea D0–D3.

Secuencia de construccion:

1. producto paralelo y su comparador con el tensor del destino;
2. trenzado natural con coherencias;
3. objetos duales, evaluacion/coevaluacion y triangulos;
4. twist con unidad y balance;
5. compatibilidad del twist con dualidad;
6. cierre de diarios y comparacion con cierre del destino;
7. traza y leyes que realmente satisface;
8. familia en rango variable y estabilizacion, cuando se reclame Markov.

En notacion estricta, el balance tiene la forma

    theta_(A tensor B)
      = (c_(B,A) o c_(A,B)) o (theta_A tensor theta_B).

En la implementacion no estricta se incluyen los transportes necesarios. El twist no es la restriccion correlativa. Dual algebraico, dagger y adjunto de operador requieren comparaciones diferentes.

Una traza ciclica puede ser insuficiente para distinguir rutas. Esta perdida no invalida su uso, pero debe registrarse. Invariancia por conjugacion a rango fijo no prueba invariancia por estabilizacion. Un control cambiando el rango debe rechazar cualquier promocion prematura a invariante general del cierre.

No se infieren nuclearidad, clase traza ni un determinante de Fredholm de un modelo finito. Esas hipotesis permanecen en CA25.

## 7. D5 — Cohomologia y observacion espectral

Dependencias: CX08 y contratos existentes de cohomologia/Hodge/espectro.

Construir primero mapas de complejos. Despues obtener la accion en cohomologia mediante los productores de cociente existentes. Una accion en el portador de cochains que no conmuta con d puede seguir siendo util como transformacion con defecto, pero no da automaticamente una accion en H^n.

Para cada grado soportado registrar:

    cochain_source
    cochain_target
    differential_comparison
    harmonic_comparison_if_any
    laplacian_intertwiner_if_any
    exchange_compatibility
    kernel_of_observation
    domain_and_finiteness_hypotheses.

Una igualdad de dimensiones de H^n es mas debil que una equivalencia de espacios; esta es mas debil que un comparador natural que intertwine los intercambios. Para preservar espectro, usar el operador y su entrelazador, no una lista de numeros. Para preservar accion en cada autoespacio, demostrar compatibilidad de ambos operadores.

Control necesario: una transformacion actua trivialmente en cohomologia y no trivialmente en el nivel de rutas o cochains. Es un objetivo de modelo, no una existencia ya demostrada en este plan. Impide confundir observacion cohomologica con reconstruccion completa del proceso.

## 8. D6 — Cactus, asociadores y completaciones

### D6-a: consumidor coboundary

Construir el commutor y verificar la coherencia cactus en un destino real. El hecho de que cada intercambio sea involutivo no basta. El corpus debe conservar un caso en que la ley trenzada no se haya probado o falle, en vez de forzar el destino a ser simetrico.

Para interpretacion geometrica, distinguir cactus J_n y puro PJ_n. La referencia de Henriques–Kamnitzer identifica la diferencia mediante una extension por S_n y un espacio clasificante orbifold; no reemplazarlo por la afirmacion de que J_n es la fundamental ordinaria del mismo espacio que PJ_n [R1 del documento principal].

### D6-b: parentizaciones y nivel superior

Construir los objetos parentizados, sus operaciones de sustitucion y las coherencias que se realizan. Un conjunto de grupos B_n sin composiciones compatibles no es una operada de trenzas. Un asociador formal sin pentagono no es un asociador coherente. Si las leyes se conservan hasta celdas superiores, indicar la dimension exacta y probar las compatibilidades adicionales.

### D6-c: realizacion profinita/aritmetica

Construir sistemas de cocientes finitos compatibles, mapas de transicion, limite y acciones continuas en el dominio requerido. Finitud de cada nivel no prueba residual finiteness ni inyectividad de la fuente en el limite; esas son obligaciones separadas. Una torre de grupos sin compatibilidad de operaciones no produce automaticamente la operada completada.

Solo despues comparar con estructuras Grothendieck–Teichmuller/Galois del destino. Los resultados externos de Horel justifican una ruta matematica posible; no identifican nuestro formalismo causal con ese objeto por el nombre de braid. No se supone que la realizacion sea conjunta o individualmente conservativa.

Este horizonte queda explicitamente planificado, no eliminado por dificultad, y no bloquea la acreditacion de consumidores finitos anteriores.

## 9. Frontera de Hecke y resto de rutas aritmeticas

Separar una relacion cuadratica de un operador de trenzado, por ejemplo

    (T_i - q_H I)(T_i + I)=0,

de la construccion de operadores Hecke aritmeticos sobre reticulas/correspondencias locales. El parametro q_H de esa presentacion no se identifica automaticamente con la cardinalidad residual q=p^f. Exigir un teorema que los conecte en un dominio comun.

Igualmente, un operador que satisfaga YB no se llama Frobenius; un exponente de trenza no se llama valuacion local sin leyes y comparador; una trenza pura no se llama Sha ni una obstruccion a YB se llama curvatura aritmetica por analogia.

Las realizaciones Tate, Tamagawa y locales/globales pueden observar nuevos invariantes de intercambio cuando exista una construccion concreta. No se añaden estos datos como parametros libres a los objetos existentes para simular una derivacion.

## 10. Matriz de informacion por dimension

La matriz por consumidor tiene que distinguir:

| Nivel | Pregunta |
|---|---|
| 0: fronteras/objetos | Puede distinguir fuentes no equivalentes en ese nivel? |
| 1: historias/diarios | Puede distinguir ejecuciones con iguales extremos? |
| 2: intercambios/rutas | Puede distinguir reorganizaciones con iguales historia inicial y final? |
| 3: comparadores | Conserva diferentes coherencias entre las mismas rutas? |
| observacion numerica | Que clases adicionales identifica la traza, dimension, indice o espectro observado? |

En cada nivel declarar la relacion concreta de igualdad/equivalencia. Fidelidad en hom-sets, reflexion de isomorfismos, conservatividad de objetos y reconstruccion no son sinonimos.

Para P,Q paralelas, el nucleo del observador es una relacion R_F(P,Q): F(P)=F(Q), o su variante de equivalencia de destino. Si H=G o F, demostrar inclusion de los nucleos con las hipotesis necesarias sobre la equivalencia elegida. Una familia (F_i) distingue una pareja si al menos un miembro la separa; reconstruir todas las rutas de un dominio necesita un teorema mas fuerte.

En el sector reversible, F(Omega)=id prueba que Omega esta en el nucleo local. Si F es fiel en ese hom-set y preserva identidades, implica Omega=id. Sin esa hipotesis se registra perdida, no se altera el teorema fuente para obtener igualdad.

## 11. Criterios de salida de cada consumidor

Cada D_i tiene un recibo independiente con:

* fuente causal concreta y dominio de enriquecimiento;
* destino nativo y declaraciones consumidas;
* mapas sobre generadores y extension a composiciones;
* leyes realmente preservadas y defectos no preservados;
* comparadores con las realizaciones anteriores;
* controles positivos y mutaciones del mismo tipo;
* matriz de perdida por dimension;
* costes del experimento, incluyendo dimensiones y certificados;
* source SHA, downstream SHA y dependencia resuelta;
* compilacion Lean y auditoria de axiomas del alcance.

La fuente de un consumidor no se puede reconstruir retrospectivamente poniendo como campo toda la estructura del destino. Debe presentarse una construccion causal y demostrar que su realizacion da el destino reclamado, o etiquetar honestamente el ejemplo como modelo/control.

No se publica un unico estado ECIA-preserves-everything. Cada propiedad tiene una fila y un dominio. Ningun gate downstream bloquea el cierre matematico de una fila puramente fuente que ya tenga sus consumidores internos y evidencia.
