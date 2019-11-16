FROM ubuntu:18.04
MAINTAINER Christian Heitman

RUN apt-get -y update && \
    apt-get install -y graphviz z3 python-pip git

RUN useradd -m barf
USER barf
WORKDIR /home/barf
ENV HOME /home/barf

RUN git clone https://github.com/programa-stic/barf-project.git && \
    cd barf-project && \
    pip install .

CMD ["/bin/bash"]
