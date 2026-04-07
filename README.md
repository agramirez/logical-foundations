# Software Foundations
My solutions for the problems from Rocq's [Software Foundations books.](https://softwarefoundations.cis.upenn.edu/)

# Project Structure
## Logical/Foundations
This is the [Software Foundations: Volume 1 - Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html) book lessons and exercises.

Each chapter corresponds to a different subfolder:

- [Basics](./Logical/Foundations/Basics/)
    - [Concepts](./Logical/Foundations/Basics/Concepts/)
        - [Data and Functions](./Logical/Foundations/Basics/Concepts/DataAndFunctions.v)
    - [Exercises](./Logical/Foundations/Basics/Exercises)
        - [Late Days](./Logical/Foundations/Basics/Exercises/LateDays.v.enc) (encrypted)
        - [NandB](./Logical/Foundations/Basics/Exercises/NandB.v.enc) (encrypted)

Within each chapter folder there is a **Concepts** directory, which is basically a copy of all the basic lessons, proofs, and definitions within the chapter.  This is not very interesting for demonstration purposes since it's essentially a copy/paste of the book.

However, within each chapter folder there is also an Exercises folder.  That is definitely interesting because it contains all of my solutions to the exercises provided in the book.

> NOTE: To prevent cheating, and as requested by the [Preface of Verified Functional Algorithms](https://softwarefoundations.cis.upenn.edu/vfa-current/Preface.html), I've encrypted my solutions to excersizes.  They can be decrypted using the [decrypt_exercises.sh](./decrypt_exercises.sh) script.  The script requires a .env file as described in [.env.example](./env.example).  The actual password to decrypt the files will be provided upon request.

## Pre-requisites
To run the Rocq code you can use VSCode with Dev Containers to launch a Dev Container with Rocq installed or you can have the Rocq IDE installed and configured on your PC and Copy/Paste the code or open it with the IDE.

For option #1 (recommended) please install

- [Docker Desktop](https://docs.docker.com/desktop/)
- [VSCode](https://code.visualstudio.com/download)
- [Container Tools VSCode Extension](https://marketplace.visualstudio.com/items?itemName=ms-azuretools.vscode-containers)

For option #2 you can find and install Rocq here:

- [Rocq Prover Install](https://rocq-prover.org/install)

The Quick Start guide works with option #1.

## Quick Start
- Launch VSCode
- Open the repo
- Hit Ctrl+Shift+P to open the Command Pallette
- Search for `Dev Containers: Open Folder in Container...`
- Select the folder where you downloaded the repo and click open

## Disclaimer

This is a work in progress as I continue learning the basics of Rocq and is intended for demonstration purposes only.

Check back for regular updates!