all : 
	coqc *.v

clean : 
	rm *.glob
	rm *.vo
	rm .*.aux
