#SCHEME=petite
SCHEME=scheme
OUTPUT=res.raw
FINAL=res.final
PRETTY=1

timeit:
	cp settings/skew-def-settings.scm settings.scm
	$(SCHEME) --script timeit.scm > $(OUTPUT) 2>&1
	cp settings/skew-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/assq-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/sref-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/sreff-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/fb-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/fb-opt-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/no-rec-stk-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/no-rec-stkf-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/pinch-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/pinch-s-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/basic-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/rhs-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/step-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/trie-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	cp settings/bst-settings.scm settings.scm
	$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1
	./process_res $(OUTPUT) $(PRETTY) | tee $(FINAL)

#cp settings/foldr-settings.scm settings.scm   # just too slow
#$(SCHEME) --script timeit.scm >> $(OUTPUT) 2>&1

quick:
	cp settings/skew-def-settings.scm settings.scm
	$(SCHEME) --script timeit.scm > quick.raw 2>&1
	./process_res quick.raw | tee quick.final

all: timeit
