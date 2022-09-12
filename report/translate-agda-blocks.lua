
-- Pandoc filter

-- Translates agda code blocks
-- from native pandoc IR to embedded LaTeX

-- Preserves code blocks labels

function CodeBlock (el)
    if el.classes[1] ~= 'agda'
    then return nil end -- Do nothing to non-agda code blocks
    
    -- Preserve labels
    lab = el.attr.identifier
    if lab == ''
    then prefix = ''
    else prefix = '\\hypertarget{' .. lab .. '}{\\label{' .. lab .. '}}'
    end

    return pandoc.RawInline('latex',
        prefix .. '\\begin{code}\n' ..  el.text .. '\n\\end{code}\n'
    )
end
