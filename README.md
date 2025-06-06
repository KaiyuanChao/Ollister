# Ollister
An intuitive Ollama model lister with a speedy GUI. 

Low system requirements: A single python file, requiring Python 3.8 or higher, no external dependencies beyond the python standard library including tKinter.

Peek inside the details of Ollama's language models models on your system, with full tensor listings and an experimental pillow-plot where the tensors are colored by quantization type and grouped by layers.
Expose all the embedded system prompts, chat templates, and hidden parameters.
See how much hard drive space the models take up with the pie chart plot.
Prune, start, or update them from the menu that pops up when you right-click the model name in the list.

A windows 11 .exe wrapper is provided with the release for convenience, but running the python file directly on your system makes for a much snappier experience. 

> python Ollister.py

Tested on Windows 11 and MacOS.

<img width="569" alt="PieChart_readme" src="https://github.com/user-attachments/assets/62749287-75de-4097-b4c9-17820e32349d" />


<img width="615" alt="TensorPlot" src="https://github.com/user-attachments/assets/1332b29a-c3cf-4d6e-9215-1dab7962ab10" />


<img width="1494" alt="OLLISTER_Screenshot" src="https://github.com/user-attachments/assets/f897d809-8b71-44e3-8282-67e504021561" />
