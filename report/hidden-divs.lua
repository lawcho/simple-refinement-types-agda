
-- Pandoc filter to transform native "hidden" divs
-- to raw LaTeX comments

-- (requires the "comment" LaTeX package) 

function Div (el)
    if el.classes:includes('hidden',0)
    then
        elts = el.content:clone()
        elts:insert(1,pandoc.Plain(pandoc.RawInline('latex','\\begin{comment}')))
        elts:insert(pandoc.Plain(pandoc.RawInline('latex','\\end{comment}')))
        return pandoc.Div(elts)
    else return nil -- Do nothing to other divs
    end
end

