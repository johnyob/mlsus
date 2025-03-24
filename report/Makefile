.DEFAULT_GOAL := all

.PHONY: all 
all:
	typst compile main.typ 

.PHONY: watch 
watch: 
	typst watch main.typ

.PHONY: clean 
clean:
	rm main.pdf