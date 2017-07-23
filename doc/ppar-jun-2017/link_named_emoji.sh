#!/usr/local/bin/bash

TWEMOJI_SOURCE_DIR='/Users/wen/Projects/twemoji/assets'
TWEMOJI_SOURCE_EXT='ai'
TWEMOJI_TARGET_DIR='/Users/wen/Projects/nodcap/doc/ppar-jun-2017'
TWEMOJI_TARGET_EXT='pdf'

declare -A TWEMOJI
TWEMOJI['1f466']='john'
TWEMOJI['1f469']='mary'
TWEMOJI['1f3e0']='patisserie'
TWEMOJI['1f4b0']='money'
TWEMOJI['1f4b7']='moneybill'
TWEMOJI['1f382']='cake'
TWEMOJI['1f370']='cakeslice'
TWEMOJI['1f64c']='nocake'

for K in "${!TWEMOJI[@]}"; do
	ln -s "${TWEMOJI_SOURCE_DIR}/${K}.${TWEMOJI_SOURCE_EXT}" "${TWEMOJI_TARGET_DIR}/${TWEMOJI[$K]}.${TWEMOJI_TARGET_EXT}"
done
