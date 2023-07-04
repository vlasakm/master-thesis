.PHONY: all zip clean

TEX = mmoptex
RM = rm -f
CD = cd

ZIP = vlasami6-dip.zip
SOURCES = README.md \
	  benchmarks \
	  examples \
	  ref \
	  src \
	  tests \
	  text/figures \
	  text/vlasami6-dip.bib \
	  text/vlasami6-dip.tex \
	  meson.build \
	  README.md \
	  test.sh \

TARGETS = text/vlasami6-dip.pdf

all: $(TARGETS)

zip: $(ZIP) Makefile
$(ZIP): $(SOURCES) $(TARGETS)
	zip -r $@ $^

text/vlasami6-dip.pdf: text/vlasami6-dip.tex text/vlasami6-dip.bib
	$(CD) text; $(TEX) vlasami6-dip; $(TEX) vlasami6-dip; $(TEX) vlasami6-dip;

clean:
	$(RM) $(TARGETS) $(ZIP) *.ref *.log src/*.ref src/*.log
