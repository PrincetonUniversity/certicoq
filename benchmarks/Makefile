all: demo demo1 demo2 vs

demo: demo.v
	coqc demo.v

demo1: maindemo1.c
	gcc -o demo1 -Wno-everything -m32 -O2 maindemo1.c gc.c demo.demo1.c

demo2: maindemo2.c
	gcc -o demo2 -Wno-everything -m32 -O2 maindemo2.c gc.c demo.demo2.c

vs: demo.is_valid.c
	gcc -o vs -Wno-everything -m32 -O2 mainvs.c gc.c demo.is_valid.c