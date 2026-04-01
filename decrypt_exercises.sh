#!/bin/bash
# Simple bash script to decrypt all exercise files
source .env

if [ -z "$ENC_PASSWORD" ] 
then
    echo "password from .env file (ENC_PASSWORD) was not found"
    exit 1
fi

echo "starting decryption and hash check"
for e in $(find -type f -path '*Exercises*' -iname '*.v.enc')
do
    ed=$(echo "$e" | sed 's/.v.enc/.v/')
    es=$(echo "$e" | sed 's/.v.enc/.sha256/')

    echo "decrypting $e to $ed"
    openssl enc -d -aes-256-cbc -pbkdf2 -base64 -nosalt -k "$ENC_PASSWORD" -in "$e" -out "$ed"
    echo "checking sha256 stored in $es"
    sha256sum -c "$es"
done

echo "done decrypting and hash checking"