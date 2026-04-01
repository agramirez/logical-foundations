#!/bin/bash
# Simple bash script to encrypt all exercise files
source .env

if [ -z "$ENC_PASSWORD" ] 
then
    echo "password from .env file (ENC_PASSWORD) was not found"
    exit 1
fi

echo "starting encruption and hash check"
for e in $(find -type f -path '*Exercises*' -iname '*.v')
do
    ed="$e.enc"
    es=$(echo "$e" | sed 's/.v/.sha256/')

    echo "checking sha256 stored in $es"
    sha256sum "$e" > "$es"

    echo "encrypting $e to $ed"
    openssl enc -aes-256-cbc -pbkdf2 -base64 -nosalt -k "$ENC_PASSWORD" -in "$e" -out "$ed"
done

echo "done encrypting and hashing"