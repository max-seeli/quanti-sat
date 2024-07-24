import os
import pandas as pd
# Arbitrary width for the pandas output
pd.set_option('display.max_rows', None)
pd.set_option('display.max_columns', None)

def is_leaf_folder(path):
    """ Check if the given path is a leaf folder (contains only files) """
    if os.path.isdir(path):
        for entry in os.listdir(path):
            # If any entry is a directory, return False
            if os.path.isdir(os.path.join(path, entry)):
                return False
        return True
    return False

def generate_reports(data_path, report_path):
    """ Summarize the contents of the given folder """
    print(f"Generating report for: {data_path}")

    files = os.listdir(data_path)
    
    all_data = pd.DataFrame(columns=['file', 'status', 'conversion_time', 'solver_time', 'num_forall_vars','num_exists_vars','num_switches'])

    for file in files:
        full_path = os.path.join(data_path, file)
        
        with open(full_path, 'r') as f:
            lines = f.readlines()
            # If there is a line with "CSV:", then parse the next line as CSV
            found = False
            for i, line in enumerate(lines):
                if "CSV:" in line:
                    csv = [s.strip() for s in lines[i+1].split(",")]
                    all_data = pd.concat([all_data, pd.DataFrame([csv], columns=all_data.columns)])
                    found = True
                    break
            if not found:
                all_data = pd.concat([all_data, pd.DataFrame([[file, "TIMEOUT", "None", "None", "None", "None", "None"]], columns=all_data.columns)])

    # Write the data to a CSV file
    solver_name = os.path.basename(data_path)
    method_name = os.path.basename(os.path.dirname(data_path))
    file_name = f"{method_name}-{solver_name}.csv"
    all_data.to_csv(os.path.join(report_path, file_name), index=False)

    return all_data
    # Print a frequency table of the status
    #print(all_data['status'].value_counts())
            


def main(directory, report_path):
    #all_tables = {}
    #status_summary = pd.DataFrame()
        
    for root, dirs, files in os.walk(directory, topdown=False):
        # Check if the current root is a leaf folder
        if is_leaf_folder(root):
            generate_reports(root, report_path=report_path)
            #summarized_data = generate_reports(root, report_path=report_path)
            #all_tables[root] = summarized_data
            #status_count = summarized_data['status'].value_counts().rename(root)
            #status_summary = pd.concat([status_summary, status_count], axis=1)

    """   
    # Compare the frequency tables of the status in one table (columns are the leaf folders and rows are the status)
    print(status_summary.fillna(0).astype(int))  # filling NaN with 0 and converting floats to int for better readability

    print("Average overall times per leaf folder:")
    for folder, table in all_tables.items():
        # Convert the times to numeric
        table['conversion_time'] = pd.to_numeric(table['conversion_time'], errors='coerce')
        table['solver_time'] = pd.to_numeric(table['solver_time'], errors='coerce')
        # Calculate the average times
        avg_conversion_time = table['conversion_time'].mean()
        avg_solver_time = table['solver_time'].mean()
        print(f"{folder}:")
        print(f"Average conversion time: {avg_conversion_time}")
        print(f"Average solver time: {avg_solver_time}")
        print()


    print("Uniquely solved files (by our approach)")
    # take the union of all correctly solved files from ['farkas-templates-deg-1',  'handelman-templates-deg-1',  'handelman-templates-deg-2']
    our_approaches = ['farkas-templates-deg-1',  'handelman-templates-deg-1',  'handelman-templates-deg-2']
    our_correct_files = set()
    for folder, table in all_tables.items():
        for our_approach in our_approaches:
            if our_approach in folder:
                our_correct_files.update(table[table['status'] == 'CORRECT']['file'])
    
    other_approaches = ['z3-skolemization']#, 'z3-skolemization-templates-deg-1', 'z3-skolemization-templates-deg-2']
    other_correct_files = set()
    for folder, table in all_tables.items():
        for other_approach in other_approaches:
            if '/' + other_approach + '/' in folder:
                other_correct_files.update(table[table['status'] == 'CORRECT']['file'])
    print(f"Our correct #{len(set(our_correct_files))}")
    print(f"Other correct #{len(set(other_correct_files))}")
    print(f"Number of uniquely solved files by our approach: {len(our_correct_files - other_correct_files)}")
                
    
    # ,  z3-skolemization  z3-skolemization-templates-deg-1  z3-skolemization-templates-deg-2


    print("Correct files of skolemization")
    correct_skol = all_tables['./data/handelman-templates-deg-1/z3'][all_tables['./data/handelman-templates-deg-1/z3']['status'] == 'PARSING_ERROR']

    # Split the 'file' column of structure 'ex%d_formula_%d.m' into two columns 'ex' and 'formula'
    correct_skol[['ex', 'formula']] = correct_skol['file'].str.extract(r'ex(\d+)_formula_(\d+).m')
    #print(correct_skol)

    # Print frequency table of the 'ex' column
    #print(correct_skol['ex'].value_counts())


    # Print the intersection of the files that are CORRECT in './data/handelman-templates-deg-1/z3' and './data/z3-skolemization/z3'

    handelman_correct_files = all_tables[directory + '/handelman-templates-deg-1/z3'][all_tables[directory + '/handelman-templates-deg-1/z3']['status'] == 'INCORRECT']
    print("Hi")
    #print(handelman_correct_files)
    print("Hi")
    farkas_incorrect_files = all_tables[directory + '/farkas-templates-deg-1/z3'][all_tables[directory + '/farkas-templates-deg-1/z3']['status'] == 'INCORRECT']
    intersection = handelman_correct_files[handelman_correct_files['file'].isin(farkas_incorrect_files['file'])]
    #print(intersection)
    print(f"Number of files in the intersection: {len(intersection)}")
"""

if __name__ == "__main__":
    results_dir = os.path.dirname(os.path.realpath(__file__))
    reports_dir = os.path.join(results_dir, "reports")
    os.makedirs(reports_dir, exist_ok=True)
    main("./data", reports_dir)


    # Use the handelman-templates-deg-1-mathsat.csv and plot on the x axis the number of switches and on the y axis the number of correct files
    handel = pd.read_csv(os.path.join(reports_dir, "handelman-templates-deg-1-mathsat.csv"))
